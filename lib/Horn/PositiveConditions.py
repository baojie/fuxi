#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
The language of positive RIF conditions determines what can appear as a body (the
 if-part) of a rule supported by the basic RIF logic. As explained in Section 
 Overview, RIF's Basic Logic Dialect corresponds to definite Horn rules, and the
  bodies of such rules are conjunctions of atomic formulas without negation.
"""
import itertools
from rdflib import Variable, BNode, URIRef, Literal, Namespace,RDF,RDFS
from rdflib.Literal import _XSD_NS
from rdflib.util import first
from rdflib.Collection import Collection
from rdflib.Graph import ConjunctiveGraph,QuotedGraph,ReadOnlyGraphAggregate, Graph
from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib.syntax.xml_names import split_uri

OWL    = Namespace("http://www.w3.org/2002/07/owl#")

def buildUniTerm((s,p,o),newNss=None):
    return Uniterm(p,[s,o],newNss=newNss)

def GetUterm(term):
    if isinstance(term,Uniterm):
        return term
    elif isinstance(term,Exists):
        return term.formula
    else:
        raise Exception("Unknown term: %s"%term)

class QNameManager(object):
    def __init__(self,nsDict=None):
        self.nsDict = nsDict and nsDict or {}
        self.nsMgr = NamespaceManager(Graph())
        self.nsMgr.bind('owl','http://www.w3.org/2002/07/owl#')
        self.nsMgr.bind('math','http://www.w3.org/2000/10/swap/math#')
        
    def bind(self,prefix,namespace):
        self.nsMgr.bind(prefix,namespace)

class SetOperator(object):
    def repr(self,operator):
        nafPrefix = self.naf and 'not ' or ''
        if len(self.formulae)==1:
            return nafPrefix+repr(self.formulae[0])
        else:
            return "%s%s( %s )"%(nafPrefix,operator,' '.join([repr(i) for i in self.formulae]))
    def remove(self,item):
        self.formulae.remove(item)
        
    def __len__(self):
        return len(self.formulae)

class Condition(object):
    """
    CONDITION   ::= CONJUNCTION | DISJUNCTION | EXISTENTIAL | ATOMIC
    """
    def isSafeForVariable(self,var):
        """
        A variable, v is safe in a condition formula if and only if ..
        """
        return False
    
    def __iter__(self):
        for f in self.formulae:
            yield f

class And(QNameManager,SetOperator,Condition):
    """
    CONJUNCTION ::= 'And' '(' CONDITION* ')'
    
    >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    And( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) )
    """
    def __init__(self,formulae=None,naf=False):
        self.naf = naf
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)

    def binds(self, var):
        """
        A variable, v, is bound in a conjunction formula, f = And(c1...cn), n ≥ 1, 
        if and only if, either

        - v is bound in at least one of the conjuncts;

        For now we don't support equality predicates, so we only check the 
        first condition
        
        >>> x=Variable('X')
        >>> y=Variable('Y')
        >>> lit1 = Uniterm(RDF.type,[x,RDFS.Class])
        >>> lit2 = Uniterm(RDF.Property,[y,RDFS.Class])
        >>> conj = And([lit1,lit2])
        >>> conj.binds(Variable('Y'))
        True
        >>> conj.binds(Variable('Z'))
        False
        """
        return first(itertools.ifilter(lambda conj: conj.binds(var),
                                       self.formulae)) is not None

    def __getitem__(self, item):
        return self.formulae[item]

    def isSafeForVariable(self,var):
        """
        A variable, v is safe in a condition formula if and only if ..
        
        f is a conjunction, f = And(c1...cn), n ≥ 1, and v is safe in at least 
        one conjunct in f
        
        Since we currently don't support equality predicates, we only check
        the first condition
        
        >>> x=Variable('X')
        >>> y=Variable('Y')
        >>> lit1 = Uniterm(RDF.type,[x,RDFS.Class])
        >>> lit2 = Uniterm(RDF.Property,[y,RDFS.Class])
        >>> conj = And([lit1,lit2])
        >>> conj.isSafeForVariable(y)
        True
                
        """
        return first(itertools.ifilter(lambda conj: conj.isSafeForVariable(var),
                                       self.formulae)) is not None
        
    def n3(self):
        """
        >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
        ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])]).n3()
        u'rdfs:comment a rdf:Property .\\n owl:Class a rdfs:Class'
        
        """
#        if not [term for term in self if not isinstance(term,Uniterm)]:
#            g= Graph(namespace_manager = self.nsMgr)
#            g.namespace_manager= self.nsMgr
#            [g.add(term.toRDFTuple()) for term in self]
#            return g.serialize(format='n3')
#        else:
        return u' .\n '.join([i.n3() for i in self])
        
    def __repr__(self):
        return self.repr('And')
    
class Or(QNameManager,SetOperator,Condition):
    """
    DISJUNCTION ::= 'Or' '(' CONDITION* ')'
    
    >>> Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    Or( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) )
    """
    def __init__(self,formulae=None,naf=False):
        self.naf = naf
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)

    def binds(self, var):
        """
        A variable, v, is bound in a disjunction formula, if and only if v is 
        bound in every disjunct where it occurs
        
        >>> x=Variable('X')
        >>> y=Variable('Y')
        >>> lit1 = Uniterm(RDF.type,[x,RDFS.Class])
        >>> lit2 = Uniterm(RDF.Property,[y,RDFS.Class])
        >>> conj = And([lit1,lit2])
        >>> disj = Or([conj,lit2])
        >>> disj.binds(y)
        True
        >>> disj.binds(Variable('Z'))
        False
        >>> lit = Uniterm(RDF.type,[OWL.Class,RDFS.Class])
        >>> disj= Or([lit,lit])
        >>> disj.binds(x)
        False
        """
        unboundConjs = list(itertools.takewhile(lambda conj: conj.binds(var),
                                                self.formulae))
        return len(unboundConjs) == len(self.formulae)

    def isSafeForVariable(self,var):
        """
        A variable, v is safe in a condition formula if and only if ..
        
        f is a disjunction, and v is safe in every disjunct;
        """
        unboundConjs = list(itertools.takewhile(
                                    lambda conj: conj.isSafeForVariable(var),
                                    self.formulae))
        return len(unboundConjs) == len(self.formulae)

        
    def __repr__(self):
        return self.repr('Or')

class Exists(Condition):
    """
    EXISTENTIAL ::= 'Exists' Var+ '(' CONDITION ')'
    >>> Exists(formula=Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...                    Uniterm(RDF.type,[OWL.Class,RDFS.Class])]),
    ...        declare=[Variable('X'),Variable('Y')])
    Exists ?X ?Y ( Or( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) ) )
    """
    def __init__(self,formula=None,declare=None):
        self.formula = formula
        self.declare = declare and declare or []

    def binds(self, var):
        """
        A variable, v, is bound in an existential formula, 
        Exists v1,...,vn (f'), n ≥ 1, if and only if v is bound in f'
        
        >>> ex=Exists(formula=And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
        ...                    Uniterm(RDF.type,[Variable('X'),RDFS.Class])]),
        ...        declare=[Variable('X')])
        >>> ex.binds(Variable('X'))
        True
        """
        return self.formula.binds(var)
    
    def isSafeForVariable(self,var):
        """
        A variable, v is safe in a condition formula if and only if ..
        
        f is an existential formula, f = Exists v1,...,vn (f'), n ≥ 1, and 
        v is safe in f' .
        """
        return self.formula.isSafeForVariable(var) 
            
    def __iter__(self):
        for term in self.formula: 
            yield term
    def n3(self):
        """
        """
        return self.formula.n3()
        #return u"@forSome %s %s"%(','.join(self.declare),self.formula.n3())
    
    def __repr__(self):
        return "Exists %s ( %r )"%(' '.join([var.n3() for var in self.declare]),
                                   self.formula )
        
class Atomic(Condition):
    """
    ATOMIC ::= Uniterm | Equal | Member | Subclass (| Frame)
    """
    def binds(self, var):
        """
        A variable, v, is bound in an atomic formula, a, if and only if
        
        - a is neither an equality nor an external predicate, and v occurs as an 
          argument in a;
        - or v is bound in the conjunction formula f = And(a).
        
        Default is False
                
        """
        return False
    
    def __iter__(self):
        yield self

class Equal(QNameManager,Atomic):
    """
    Equal ::= TERM '=' TERM
    TERM ::= Const | Var | Uniterm | 'External' '(' Expr ')'
    
    >>> Equal(RDFS.Resource,OWL.Thing)
    rdfs:Resource =  owl:Thing
    """
    def __init__(self,lhs=None,rhs=None):
        self.lhs = lhs
        self.rhs = rhs
        QNameManager.__init__(self)
        
    def __repr__(self):
        left  = self.nsMgr.qname(self.lhs)
        right = self.nsMgr.qname(self.rhs)
        return "%s =  %s"%(left,right)

def BuildUnitermFromTuple((s,p,o),newNss=None):
    return Uniterm(p,[s,o],newNss)

def compute_qname(uri,revNsMap):
    namespace, name = split_uri(uri)
    namespace = URIRef(namespace)
    prefix = revNsMap.get(namespace)
    if prefix is None:
        prefix = "_%s" % len(revNsMap)
        revNsMap[namespace]=prefix
    return (prefix, namespace, name)

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
            try:
                qNameParts = compute_qname(rdfTerm,revNsMap)
                return ':'.join([qNameParts[0],qNameParts[-1]])
            except:
                for ns in revNsMap:
                    if rdfTerm.find(ns)+1:
                        return ':'.join([revNsMap[ns],rdfTerm.split(ns)[-1]])
                return "<%s>"%rdfTerm
    prefix = revNsMap.get(namespace)
    if prefix is None and isinstance(rdfTerm,Variable):
        return "?%s"%rdfTerm
    else:
        qNameParts = compute_qname(rdfTerm,revNsMap)
        return ':'.join([qNameParts[0],qNameParts[-1]])

def renderTerm(graph,term):
    if isinstance(term,URIRef):
        return normalizeUri(term,hasattr(graph,'revNsMap') and graph.revNsMap or\
                                  dict([(u,p) for p,u in graph.namespaces()]))
    elif isinstance(term,Literal):
        return term._literal_n3(use_plain=True)
    else:
        try:
            if isinstance(term,BNode):
                return term.n3()
            else:
                return graph.qname(term)
        except:
            return term.n3()

class Uniterm(QNameManager,Atomic):
    """
    Uniterm ::= Const '(' TERM* ')'
    TERM ::= Const | Var | Uniterm
    
    We restrict to binary predicates (RDF triples)
    
    >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property])
    rdf:Property(rdfs:comment)
    """
    def __init__(self,op,arg=None,newNss=None,naf=False):
        self.naf = naf
        self.op = op
        self.arg = arg and arg or []
        QNameManager.__init__(self)
        if newNss is not None:
            if isinstance(newNss,NamespaceManager):
                self.nsMgr = newNss
            else:
                newNss = newNss.items() if isinstance(newNss,dict) else newNss
                for k,v in newNss:
                    self.nsMgr.bind(k,v)
        self._hash=hash(reduce(lambda x,y:str(x)+str(y),
            len(self.arg)==2 and self.toRDFTuple() or [self.op]+self.arg))
        self.herbrand_hash=hash(
            reduce(
                lambda x,y:str(x)+str(y),
                filter(lambda i:not isinstance(i,Variable),
                    self.toRDFTuple() if len(self.arg)==2
                    else [self.op]+self.arg),None))

    def binds(self, var):
        """
        A variable, v, is bound in an atomic formula, a, if and only if
        
        - a is neither an equality nor an external predicate, and v occurs as an 
          argument in a;
        - or v is bound in the conjunction formula f = And(a).
        
        Default is False
        
        >>> x = Variable('X')
        >>> lit = Uniterm(RDF.type,[RDFS.comment,x])
        >>> lit.binds(Variable('Z'))
        False
        >>> lit.binds(x)
        False
        >>> Uniterm(RDF.type,[x,RDFS.Class]).binds(x)
        True
        
        """
        if self.op == RDF.type:
            arg0,arg1 = self.arg
            return var == arg0            
        else:
            return var in self.arg
        
    def isSafeForVariable(self,var):
        """
        A variable, v is safe in a condition formula if and only if ..
        
        f is an atomic formula and f is not an equality formula in which both 
        terms are variables, and v occurs in f;
        """
        return self.binds(var)
        
    def renameVariables(self,varMapping):
        if self.op == RDF.type:
            self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
        else:
            self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
            self.arg[1]=varMapping.get(self.arg[1],self.arg[1])
        #Recalculate the hash after modification
        self._hash=hash(reduce(lambda x,y:str(x)+str(y),
            len(self.arg)==2 and self.toRDFTuple() or [self.op]+self.arg))
            
            
    def _get_terms(self):
        """
        Class attribute that returns all the terms of the literal as a lists
        >>> x = Variable('X')
        >>> lit = Uniterm(RDF.type,[RDFS.comment,x])
        >>> lit.terms
        [rdflib.URIRef('http://www.w3.org/1999/02/22-rdf-syntax-ns#type'), rdflib.URIRef('http://www.w3.org/2000/01/rdf-schema#comment'), ?X]
        """
        return [self.op]+self.arg
            
    terms = property(_get_terms)

    def unify(self,otherLit):
        """
        Takes another (ground) Uniterm and returns the substitutions that need to be applied
        to this (non-ground) one to convert to the other (i.e., unifies the two)
        
        >>> x = Variable('X')
        >>> y = Variable('Y')
        >>> lit1 = Uniterm(RDF.type,[RDFS.comment,x])
        >>> lit2 = Uniterm(RDF.type,[RDFS.comment,RDF.Property])
        >>> lit1.unify(lit2)[x] == RDF.Property
        True
        """
        map = {}
        if isinstance(self.op,Variable) and self.op != otherLit.op:
            map[self.op] = otherLit.op
        if isinstance(self.arg[0],Variable) and self.arg[0] != otherLit.arg[0]:
            map[self.arg[0]] = otherLit.arg[0]
        if isinstance(self.arg[1],Variable) and self.arg[1] != otherLit.arg[1]:
            map[self.arg[1]] = otherLit.arg[1]
        return map        
            
    def getVarMapping(self,otherLit, reverse=False):
        """
        Takes another Uniterm and in every case where the corresponding term 
        for both literals are different variables, we map from the variable
        for *this* uniterm to the corresponding variable of the other.
        The mapping will go in the other direction if the reverse
        keyword is True
          
        >>> x = Variable('X')
        >>> y = Variable('Y')
        >>> lit1 = Uniterm(RDF.type,[RDFS.comment,x])
        >>> lit2 = Uniterm(RDF.type,[RDFS.comment,y])
        >>> lit1.getVarMapping(lit2)[x] == y
        True
        >>> lit1.getVarMapping(lit2,True)[y] == x
        True
        """
        map = {}
        if isinstance(self.op,Variable) and isinstance(otherLit.op,Variable) and \
            self.op != otherLit.op:
            if reverse:
                map[otherLit.op] = self.op 
            else:
                map[self.op] = otherLit.op
        if isinstance(self.arg[0],Variable) and isinstance(otherLit.arg[0],Variable) \
            and self.arg[0] != otherLit.arg[0]:
            if reverse:
                map[otherLit.arg[0]] = self.arg[0]
            else:
                map[self.arg[0]] = otherLit.arg[0]
        if isinstance(self.arg[1],Variable) and isinstance(otherLit.arg[1],Variable) and \
            self.arg[1] != otherLit.arg[1]:
            if reverse:
                map[otherLit.arg[1]] = self.arg[1] 
            else:
                map[self.arg[1]] = otherLit.arg[1]
        return map

    def applicableMapping(self,mapping):
        """
        Can the given mapping (presumably from variables to terms) be applied?
        """
        return bool(set(mapping).intersection([self.op]+self.arg))        

    def ground(self,varMapping):
        appliedKeys = set([self.op]+self.arg).intersection(varMapping.keys())
        self.op    =varMapping.get(self.op,self.op)
        self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
        self.arg[1]=varMapping.get(self.arg[1],self.arg[1])
        #Recalculate the hash after modification
        self._hash=hash(reduce(lambda x,y:str(x)+str(y),
            len(self.arg)==2 and self.toRDFTuple() or [self.op]+self.arg))        
        return appliedKeys
            
    def isGround(self):
        for term in [self.op]+self.arg:
            if isinstance(term,Variable):
                return False
        return True
                
    def __hash__(self):
        return self._hash
    
    def __eq__(self,other):
        return hash(self) == hash(other)                       
        
    def renderTermAsN3(self,term):
        if term == RDF.type:
            return 'a'
        elif isinstance(term, (BNode,Literal,Variable)):
            return term.n3()
        else:
            return self.nsMgr.qname(term)
        
    def n3(self):
        """
        Serialize as N3 (using available namespace managers)
        
        >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property]).n3()
        u'rdfs:comment a rdf:Property'

        """
        return ' '.join([ self.renderTermAsN3(term) 
                         for term in [self.arg[0],self.op,self.arg[1]]])
        
    def toRDFTuple(self):
        subject,_object = self.arg
        return (subject,self.op,_object)
        
    def collapseName(self,val):
        try:
            rt = self.nsMgr.qname(val)
            if len(rt.split(':')[0])>1 and rt[0]=='_':
                return u':'+rt.split(':')[-1]
            else:
                return rt
                
        except:
            for prefix,uri in self.nsMgr.namespaces():
                if val.startswith(uri):
                    return u'%s:%s'%(prefix,val.split(uri)[-1])
            return val
        
    def normalizeTerm(self,term):
        return renderTerm(Graph(namespace_manager=self.nsMgr),term)

    def getArity(self):
        return 1 if self.op == RDF.type else 2
        
    arity = property(getArity)
   
    def setOperator(self,newOp):
        if self.op == RDF.type:
            self.arg[-1] = newOp
        else:
            self.op = newOp
        
    def isSecondOrder(self):
        if self.op == RDF.type:
            return isinstance(self.arg[-1],Variable)
        else:
            return isinstance(self.op,Variable)
        
    def __repr__(self):
        negPrefix = self.naf and 'not ' or ''
        if self.op == RDF.type:
            arg0,arg1 = self.arg
            return "%s%s(%s)"%(negPrefix,self.normalizeTerm(arg1),self.normalizeTerm(arg0))
        else:
            return "%s%s(%s)"%(negPrefix,self.normalizeTerm(self.op),
                                ' '.join([self.normalizeTerm(i) for i in self.arg]))
            
class PredicateExtentFactory(object):
    """
    Creates an object which when indexed returns
    a Uniterm with the 'registered' symbol and
    two-tuple argument
    
    >>> from rdflib import Namespace, URIRef
    >>> EX_NS = Namespace('http://example.com/')
    >>> ns = {'ex':EX_NS}
    >>> somePredFactory = PredicateExtentFactory(EX_NS.somePredicate,newNss=ns)
    >>> somePredFactory[(EX_NS.individual1,EX_NS.individual2)]
    ex:somePredicate(ex:individual1 ex:individual2)
    >>> somePred2Factory = PredicateExtentFactory(EX_NS.somePredicate,binary=False,newNss=ns)
    >>> somePred2Factory[EX_NS.individual1]
    ex:somePredicate(ex:individual1)
    
    """
    def __init__(self,predicateSymbol,binary=True,newNss=None):
        self.predicateSymbol = predicateSymbol
        self.binary = binary
        self.newNss = newNss
        
    def term(self, name):
        return Class(URIRef(self + name))

    def __getitem__(self, args):
        if self.binary:
            arg1,arg2=args
            return Uniterm(self.predicateSymbol,[arg1,arg2],newNss=self.newNss)
        else:
            return Uniterm(RDF.type,[args,self.predicateSymbol],newNss=self.newNss)
                        
class ExternalFunction(Uniterm):
    """
    An External(ATOMIC) is a call to an externally defined predicate, equality, 
    membership, subclassing, or frame. Likewise, External(Expr) is a call to an 
    externally defined function.
    >>> ExternalFunction(Uniterm(URIRef('http://www.w3.org/2000/10/swap/math#greaterThan'),[Variable('VAL'),Literal(2)]))
    math:greaterThan(?VAL 2)
    """
    def __init__(self,builtin,newNss=None):
        from FuXi.Rete.RuleStore import N3RuleStore,N3Builtin
        self.builtin= builtin
        if isinstance(builtin,N3Builtin):
            Uniterm.__init__(self,builtin.uri,[builtin.argument,builtin.result])
        else:
            Uniterm.__init__(self,builtin.op,builtin.arg)
        QNameManager.__init__(self)
        if newNss is not None:
            newNss = isinstance(newNss,dict) and newNss.items() or newNss
            for k,v in newNss:
                self.nsMgr.bind(k,v)
            
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()