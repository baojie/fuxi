import copy
from itertools import chain, takewhile
from FuXi.Horn.PositiveConditions import QNameManager,SetOperator, Condition, Or, And, Uniterm, BuildUnitermFromTuple
from FuXi.Rete.RuleStore import N3Builtin
from FuXi.Rete.Util import selective_memoize
from FuXi.Rete.RuleStore import *
from FuXi.Rete.Proof import ImmutableDict
from FuXi.Rete.Magic import AdornedUniTerm
from rdflib import URIRef, RDF, Namespace, Variable, Literal
from rdflib.syntax.xml_names import split_uri
from rdflib.util import first
from FuXi.Rete.BetaNode import project
from FuXi.Rete.SidewaysInformationPassing import GetArgs, iterCondition, GetOp, GetVariables

def normalizeBindingsAndQuery(vars,bindings,conjunct):
    """
    Takes a query in the form of a list of variables to bind to
    an a priori set of bindings and a conjunct of literals and applies the bindings
    returning:
     - The remaining variables that were not substituted
     - The (possibly grounded) conjunct of literals
     - The bindings minus mappings involving substituted variables 
    
    """
    _vars = set(vars)
    bindingDomain = set(bindings.keys())
    appliedBindings = False
    if bindings:
        #Apply a priori substitutions
        for lit in conjunct:
            substitutedVars = bindingDomain.intersection(lit.toRDFTuple())
            lit.ground(bindings)
            if substitutedVars:
                appliedBindings = True
                _vars.difference_update(substitutedVars)
    return list(_vars),conjunct, \
           project(bindings,_vars,inverse=True) if appliedBindings else bindings

def tripleToTriplePattern(graph,term,specialBNodeHandling=None):
   if isinstance(term,N3Builtin):
       template = graph.templateMap[term.uri]
       return "FILTER(%s)"%(template%(term.argument.n3(),
                                      term.result.n3()))
   else:
       return "%s %s %s"%tuple([renderTerm(graph,
                                           term,
                                           predTerm=idx==1,
                                           specialBNodeHandling=specialBNodeHandling) 
                                   for idx,term in enumerate(term.toRDFTuple())])

@selective_memoize([0])
def normalizeUri(rdfTerm,revNsMap):
   """
   Takes an RDF Term and 'normalizes' it into a QName (using the registered prefix)
   or (unlike compute_qname) the Notation 3 form for URIs: <...URI...> 
   """
   try:
       namespace, name = split_uri(rdfTerm)
       namespace = URIRef(namespace)
   except:
       if isinstance(rdfTerm,Variable):
           return "?%s"%rdfTerm
       else:
           return "<%s>"%rdfTerm
   prefix = revNsMap.get(namespace)
   if prefix is None and isinstance(rdfTerm,Variable):
       return "?%s"%rdfTerm
   elif prefix is None:
       return "<%s>"%rdfTerm
   else:
       qNameParts = compute_qname(rdfTerm,revNsMap)         
       return ':'.join([qNameParts[0],qNameParts[-1]])    

@selective_memoize([0])
def compute_qname(uri,revNsMap):
   namespace, name = split_uri(uri)
   namespace = URIRef(namespace)
   prefix = revNsMap.get(namespace)
   if prefix is None:
       prefix = "_%s" % len(revNsMap)
       revNsMap[namespace]=prefix
   return (prefix, namespace, name)

def renderTerm(graph,term,predTerm=False,specialBNodeHandling=None):
   if term == RDF.type and predTerm:
       return ' a '
   elif isinstance(term,URIRef):
       qname = normalizeUri(term,hasattr(graph,'revNsMap') and graph.revNsMap or \
                            dict([(u,p) for p,u in graph.namespaces()]))
       return qname[0] == '_' and u"<%s>"%term or qname
   elif isinstance(term,Literal):
       return term.n3()
   else:
       try:
           if isinstance(term,BNode):
               return term.n3(
                   ) if specialBNodeHandling is None else specialBNodeHandling[0](
                        term)
           else:
               return graph.qname(term)
       except:
           return term.n3()

def RDFTuplesToSPARQL(conjunct, 
                     edb, 
                     isGround=False, 
                     vars=[],
                     symmAtomicInclusion=False,
                     specialBNodeHandling=None):
   """
   Takes a conjunction of Horn literals and returns the 
   corresponding SPARQL query 
   """
   queryType = isGround and "ASK" or "SELECT %s"%(' '.join([v.n3() 
                                                            for v in vars]))
   queryShell = len(conjunct)>1 and "%s {\n%s\n}" or "%s { %s }"

   if symmAtomicInclusion:
       if vars:
           var = vars.pop()
           prefix = "%s a ?KIND"%var.n3()
       else:

           prefix = "%s a ?KIND"%first([first(iterCondition(lit)).arg[0].n3() for lit in conjunct])
       conjunct = ( i.formulae[0] if isinstance(i,And) else i for i in conjunct )
       subquery = queryShell%(queryType,
                              "%s\nFILTER(%s)"%(
                            prefix,
                            ' ||\n'.join([
                              '?KIND = %s'%edb.qname(GetOp(lit)) 
                                   for lit in conjunct])))        
   else: 
       subquery = queryShell%(queryType,' .\n'.join(['\t'+tripleToTriplePattern(
                                                             edb,
                                                             lit,
                                                             specialBNodeHandling) 
                                 for lit in conjunct ]))
   return subquery

#@selective_memoize([0,1],['vars','symmAtomicInclusion'])
def RunQuery(subQueryJoin,
            bindings,
            factGraph,
            vars=None,
            debug = False,
            symmAtomicInclusion = False,
            specialBNodeHandling = None,
            toldBNode = False):
    initialNs = hasattr(factGraph,'nsMap') and factGraph.nsMap or \
               dict([(k,v) for k,v in factGraph.namespaces()])

    if not subQueryJoin:
        return False
    if not vars:
        vars=[]
    if bool(bindings):
        #Apply a priori substitutions
        openVars,conjGroundLiterals,bindings  = \
                normalizeBindingsAndQuery(set(vars),
                                          bindings,
                                          subQueryJoin)
        vars=list(openVars)
    else:
        conjGroundLiterals = subQueryJoin
    isGround = not vars
    subquery = RDFTuplesToSPARQL(conjGroundLiterals,
                                 factGraph,
                                 isGround,
                                 [v for v in vars],
                                 symmAtomicInclusion,
                                 specialBNodeHandling)

    if toldBNode:
        from rdflib.sparql.bison.Query import Prolog
        from rdflib.sparql.parser import parse
        parsedQuery = parse(subquery)
        if not parsedQuery.prolog:
            parsedQuery.prolog = Prolog(None, [])

        parsedQuery.prolog.toldBNodes = True
        subquery = ''
    else:
        parsedQuery = None

    rt = factGraph.query(subquery,
                         initNs = initialNs,
                         parsedQuery=parsedQuery)
    projectedBindings = vars and project(bindings,vars) or bindings
    if isGround:
        if debug:
            print >>sys.stderr, "%s%s-> %s"%(
                         subquery,
                         projectedBindings and 
                         " %s apriori binding(s)"%len(projectedBindings) or '',
                         rt.askAnswer[0])
        return subquery,rt.askAnswer[0]
    else:
        rt = len(vars)>1 and (
         dict([(vars[idx],
                specialBNodeHandling[-1](i)
                if specialBNodeHandling and isinstance(i,BNode)
                else i)
                                       for idx,i in enumerate(v)])
                                            for v in rt ) \
               or ( dict([(vars[0],
                           specialBNodeHandling[-1](v)
                          if specialBNodeHandling and isinstance(v,BNode) else v)
                          ]) for v in rt )
        if debug:
            print >>sys.stderr, "%s%s-> %s"%(
                   subquery,
                   projectedBindings and 
                   " %s apriori binding(s)"%len(projectedBindings) or '',                                
                   rt and '[]')# .. %s answers .. ]'%len(rt) or '[]')
        return subquery,rt

def EDBQueryFromBodyIterator(factGraph,remainingBodyList,derivedPreds,hybridPredicates=None):
    hybridPredicates = hybridPredicates if hybridPredicates is not None else []
    def sparqlResolvable(literal):
        predTerm = GetOp(literal)
        if not isinstance(literal,
                          AdornedUniTerm) and isinstance(literal,
                                                         Uniterm):
            return not literal.naf and (
                predTerm not in derivedPreds or
                ( predTerm in hybridPredicates and
                  not predTerm.find('_derived') + 1 ))
        else:
            return isinstance(literal,N3Builtin) and \
                   literal.uri in factGraph.templateMap
    def sparqlResolvableNoTemplates(literal):
        predTerm = GetOp(literal)
        if isinstance(literal,Uniterm):
            return not literal.naf and (
                predTerm not in derivedPreds or 
                ( predTerm in hybridPredicates and
                  not predTerm.find('_derived') + 1 ))
        else:
            return False
    return list(
                 takewhile(
                     hasattr(factGraph,'templateMap') and sparqlResolvable or \
                     sparqlResolvableNoTemplates,
                     remainingBodyList))

class ConjunctiveQueryMemoize(object):
    """
    Ideas from MemoizeMutable class of Recipe 52201 by Paul Moore and
    from memoized decorator of http://wiki.python.org/moin/PythonDecoratorLibrary

    A memoization decorator of a function which take (as argument): a
    graph and a conjunctive query and returns a generator over results of evaluating
    the conjunctive query against the graph
    """
    def __init__(self,cache = None):
        self._cache = cache if cache is not None else {}

    def produceAnswersAndCache(self,answers,key,cache=None):
        cache = cache if cache is not None else []
        for item in answers:
            self._cache.setdefault(key,cache).append(item)
            yield item

    def __call__(self, func):
        def innerHandler(queryExecAction,conjQuery):
            key = (conjQuery.factGraph.identifier,conjQuery)
            try:
                rt = self._cache.get(key)
                if rt is None:
                    for item in self.produceAnswersAndCache(
                            func(queryExecAction,
                                 conjQuery),
                            key):
                        yield item                    
                else:
                    for item in rt:
                        yield item                    
            except TypeError, e:
                import pickle
                try:
                    dump = pickle.dumps(key)
                except pickle.PicklingError:
                    for item in func(queryExecAction,conjQuery):
                        yield item
                else:
                    if dump in self._cache:
                        for item in self._cache[dump]:
                            yield item
                    else:
                        for item in self.produceAnswersAndCache(
                                func(queryExecAction,
                                     conjQuery),
                                dump):
                            yield item
        return innerHandler

class EDBQuery(QNameManager,SetOperator,Condition):
    """
    A list of frames (comprised of EDB predicates) meant for evaluation over a large EDB
    
    lst is a conjunct of terms
    factGraph is the RDF graph to evaluate queries over
    returnVars is the return variables (None, the default, will cause the list
     to be built via instrospection on lst)
    bindings is a solution mapping to apply to the terms in lst

    
    """
    def __init__(self, 
                 lst, 
                 factGraph,                  
                 returnVars=None, 
                 bindings={}, 
                 varMap={}, 
                 symIncAxMap = {}, 
                 symmAtomicInclusion = False,
                 specialBNodeHandling = None):
        self.factGraph            = factGraph
        self.varMap               = varMap
        self.symmAtomicInclusion  = symmAtomicInclusion
        self.formulae             = lst
        self.naf                  = False
        self.specialBNodeHandling = specialBNodeHandling

        #apply an apriori solutions
        if bool(bindings):
            #Apply a priori substitutions
            openVars,termList,bindings  = \
                    normalizeBindingsAndQuery(set(returnVars) 
                        if returnVars else [v for v in self.getOpenVars()],
                                              bindings,
                                              lst)
            self.returnVars = list(openVars)
        else:
            if returnVars is None:
                #return vars not specified, but meant to be determined by 
                #constructor 
                self.returnVars = self.getOpenVars()
            else:
                #Note if returnVars is an empty list, this
                self.returnVars = (returnVars if isinstance(returnVars,list) 
                                      else list(returnVars)) if returnVars else []
            termList = lst
            
        super(EDBQuery, self).__init__(termList)
        self.bindings            = bindings.normalize() \
                                        if isinstance(
                                            bindings,
                                            ImmutableDict) else bindings

    def copy(self):
        """
        A shallow copy of an EDB query
        """
        return EDBQuery([copy.deepcopy(t) for t in self.formulae],
                        self.factGraph,
                        self.returnVars,
                        self.bindings.copy(),
                        self.varMap.copy(),
                        symmAtomicInclusion = self.symmAtomicInclusion)
        
    def renameVariables(self, varMap):
        for item in self.formulae:
            item.renameVariables(varMap)
        
    def ground(self,mapping):
        appliedVars = set()
        for item in self.formulae:
            if isinstance(item,Or):
                for _item in item.formulae:
                    appliedVars.update(item.ground(mapping))
            else:
                appliedVars.update(item.ground(mapping))
        self.bindings = project(self.bindings,appliedVars,True)
        self.returnVars = self.getOpenVars()
        return appliedVars
                
    def accumulateBindings(self, bindings):
        """
        """
        self.bindings.update(project(bindings,self.getOpenVars(),inverse=True))

    def getOpenVars(self):
        return list(
                 set(
                   reduce(
                     lambda x,y:x+y,
                     map(lambda arg:list(GetVariables(arg,secondOrder=True)),
                         self.formulae))))

    def applyMGU(self,substitutions):
        for term in self.formulae:
            term.renameVariables(substitutions)
        self.bindings = dict([(substitutions.get(k,k),v) 
                            for k,v in self.bindings.items()])

    def evaluate(self,
                 debug = False,
                 symmAtomicInclusion = False,
                 toldBNode = False):
        import time, warnings
        from urllib2 import HTTPError
        from BaseHTTPServer import BaseHTTPRequestHandler 
        from cStringIO import StringIO
        strBuffer = StringIO()
        for attempt in range(10):
            try:
                rt = RunQuery(self.formulae,
                              self.bindings,
                              self.factGraph,
                              vars=self.returnVars,
                              debug = debug,
                              symmAtomicInclusion = symmAtomicInclusion,
                              specialBNodeHandling=self.specialBNodeHandling,
                              toldBNode=toldBNode)
                return rt
            except Exception, e:# HTTPError, e:
                #responseMsg = BaseHTTPRequestHandler.responses[e.code]
                # warnings.warn(
                # "On attempt %s Recieved HTTP response code %s from server: %s"%(
                #     attempt+1,
                #     e.code,
                #     responseMsg),
                #     RuntimeWarning,2)
                import pickle, traceback, sys
                # print "----------"*3
                traceback.print_exc(file=strBuffer)
                # print "----------"*3
                
                warnings.warn(
                "Recieved HTTP error from server",
                    RuntimeWarning,2)
                time.sleep(1)
            else: # we tried, and we had no failure, so
                break
        else: # we never broke out of the for loop
            strBuffer.write(self.asSPARQL())
            f=open('error-at-endpoint.txt','w')
            f.write(strBuffer.getvalue())
            f.close()
            raise RuntimeError(
                "Maximum number of unsuccessful attempts to evaluate %s reached."%(
                    self))        
        
    def asSPARQL(self):
        initialNs = hasattr(self.factGraph,'nsMap') and self.factGraph.nsMap or \
                    dict([(k,v) for k,v in self.factGraph.namespaces()])
        return RDFTuplesToSPARQL(self.formulae,
                                 self.factGraph,
                                 not self.returnVars,
                                 self.returnVars,
                                 self.symmAtomicInclusion,
                                 specialBNodeHandling=self.specialBNodeHandling)
        
    def __len__(self):
        return len(self.formulae)

    def __eq__(self,other):
        return hash(self) == hash(other)

    def __hash__(self):
        """
        >>> g = Graph()
        >>> lit1 = (Variable('X'),RDF.type,Variable('Y'))
        >>> q1 = EDBQuery([BuildUnitermFromTuple(lit1)],g)
        >>> q2 = EDBQuery([BuildUnitermFromTuple(lit1)],g)
        >>> q1 == q2
        True
        >>> d = {q1:True}
        >>> q2 in d
        True

        """
        from FuXi.Rete.Network import HashablePatternList
        hasBNodes = False
        for tp in self.formulae:
            for term in tp.toRDFTuple():
                if isinstance(term,BNode):
                    hasBNodes = True 
        conj=HashablePatternList(
                    [term.toRDFTuple() for term in self.formulae],
                    skipBNodes=not hasBNodes)
        return hash(conj)
        
    def extend(self, query, newVarMap = None):
        assert not query.symmAtomicInclusion  
        assert not self.symmAtomicInclusion  
        if newVarMap:
            query.renameVariables(newVarMap)
            self.varMap.update(newVarMap)
        self.formulae.extend([term for term in query.formulae 
                                if term not in self.formulae])
        self.bindings.update(query.bindings)
        
    def __repr__(self):
        return "EDBQuery(%s%s)"%(self.repr(self.symmAtomicInclusion and 'Or' or 'And'),
                       self.bindings and ',%s'%self.bindings or '')
        
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()