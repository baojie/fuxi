import doctest
from rdflib.Graph import Graph
from rdflib import RDF, URIRef, Namespace, Literal, BNode
from FuXi.Horn.PositiveConditions import GetUterm, Exists
from FuXi.Rete.Network import _mulPatternWithSubstitutions, InferredGoal
from FuXi.DLP import SKOLEMIZED_CLASS_NS
try:
    from hashlib import md5 as createDigest
except:
    from md5 import new as createDigest

class BNodeSkolemizationAction(object):
    """
    Production rule action that skolemizes blank nodes in the
    head of a rule, using a hash of the values bound to variables
    (in HornRules.py order)
    """
    def __init__(self,network):
        self.skolemTerms = set()
        for tNode in network.terminalNodes:
            for rule in tNode.rules:
                if isinstance(rule.formula.head,Exists):
                    network.registerReteAction(
                        tuple([None if isinstance(term,BNode) else term
                               for term in GetUterm(rule.formula.head).toRDFTuple()]),
                        True,
                        self)

    def __call__(self, tNode, inferredTriple, token, binding, debug):
        bnodeEncountered = {}
        bnodeCounter     = 0
        for headTriple in tNode.consequent:
            for inferredTriple,binding in _mulPatternWithSubstitutions(
                token,
                headTriple,
                tNode):
                skolemInput = u''.join(map(lambda item: binding[item],
                    sorted([key for key in binding
                            if isinstance(binding[key],URIRef) and
                               binding[key] not in self.skolemTerms])))
                if skolemInput:
                    skolemInput = createDigest(skolemInput.encode('utf-8')
                    ).hexdigest()
                    for term in inferredTriple:
                        if isinstance(term,BNode) and term not in bnodeEncountered:
                            bnodeCounter += 1
                            bnodeEncountered[term] = str(bnodeCounter)
                    inferredTriple = tuple(
                        map(lambda item: SKOLEMIZED_CLASS_NS[
                                         skolemInput+'_'+bnodeEncountered[item]]
                        if item in bnodeEncountered else item,
                            inferredTriple))
                    self.skolemTerms.update([term for term in inferredTriple
                                             if term.find(SKOLEMIZED_CLASS_NS)+1])
                    tNode.network.handleInferredTriple(
                        inferredTriple,
                        token,
                        tNode,
                        binding,
                        debug)

def IdentifyHybridPredicates(graph,derivedPredicates):
    """
    Takes an RDF graph and a list of derived predicates and return
    those predicates that are both EDB (extensional) and IDB (intensional) predicates.
    i.e., derived predicates that appear in the graph
    
    >>> g=Graph()
    >>> EX= Namespace('http://example.com/')
    >>> g.add((BNode(),EX.predicate1,Literal(1)))
    >>> g.add((BNode(),RDF.type,EX.Class1))
    >>> g.add((BNode(),RDF.type,EX.Class2))
    >>> rt=IdentifyHybridPredicates(g,[EX.predicate1,EX.Class1,EX.Class3])
    >>> sorted(rt)
    [rdflib.URIRef('http://example.com/Class1'), rdflib.URIRef('http://example.com/predicate1')]
    """
    derivedPredicates = derivedPredicates if isinstance(derivedPredicates,
                                                        set) else \
                        set(derivedPredicates)
    return derivedPredicates.intersection(                    
                    [ o if p == RDF.type else p 
                        for s,p,o in graph ])    
    
if __name__ == '__main__':
    import doctest
    doctest.testmod()