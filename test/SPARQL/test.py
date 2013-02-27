"""
FuXi Harness for W3C SPARQL1.1 Entailment Evaluation Tests
"""

import unittest, datetime
from pyparsing import ParseException
from pprint import pprint
from urllib2 import urlopen
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.Proof import ImmutableDict
from FuXi.SPARQL.BackwardChainingStore import *
from FuXi.Rete.Util import setdict
from rdflib.Namespace import Namespace
from rdflib.Collection import Collection
from rdflib import RDF,RDFS,URIRef,Variable,BNode,Literal
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate
from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib.sparql.parser import parse
from rdflib.OWL import OWLNS
from amara.lib import U

DC        = Namespace('http://purl.org/dc/elements/1.1/')
MANIFEST  = Namespace('http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#')
QUERY     = Namespace('http://www.w3.org/2001/sw/DataAccess/tests/test-query#')
SD        = Namespace('http://www.w3.org/ns/sparql-service-description#')
TEST      = Namespace('http://www.w3.org/2009/sparql/docs/tests/data-sparql11/entailment/manifest#')
STRING    = Namespace('http://www.w3.org/2000/10/swap/string#')
ENT       = Namespace('http://www.w3.org/ns/entailment/')
EARL      = Namespace('http://www.w3.org/ns/earl#')
MY_FOAF   = Namespace('http://metacognition.info/public_rdf/n3/foaf.ttl#')

SUPPORTED_ENTAILMENT=[
    ENT.RDF,
    ENT.RIF,
    ENT.RDFS,
    ENT['OWL-RDF-Based']
]

COMPLETION_RULES = [
    "sparqldl-02"
]

SKIP={
    "rdf01" : "Quantification over predicates",
    "rdfs01": "Quantification over predicates",
    "rdf02" : "Reification",
    "rdfs05": "Quantification over predicates (unary)",
    "rdfs11": "Reflexivity of rdfs:subClassOf (?x -> rdfs:Container)",
    "sparqldl-Q1"  : "Infinite loop?"
}

nsMap = {
  u'rdfs' :RDFS.RDFSNS,
  u'rdf'  :RDF.RDFNS,
  u'owl'  :OWLNS,
  u'mf'   :MANIFEST,
  u'sd'   :SD,
  u'test' :MANIFEST,
  u'qt'   :QUERY
}
MANIFEST_QUERY = \
"""
SELECT ?test ?name ?queryFile ?rdfDoc ?regime ?result
WHERE {
  ?test
    a test:QueryEvaluationTest;
      mf:name ?name;
      mf:action [
        qt:query ?queryFile;
        qt:data  ?rdfDoc;
        sd:entailmentRegime ?regime
      ];
      mf:result ?result
} ORDER BY ?test """

MANIFEST_NAMED_GRAPHS_QUERY =\
"""
SELECT ?sourceUri ?graphIri {
    %s mf:action [
        qt:graphData [
            qt:graph   ?sourceUri;
            rdfs:label ?graphIri;
        ]
    ]
}"""

PERSON_AND_PROJECT =\
"""
@prefix myfoaf: <http://metacognition.info/public_rdf/n3/foaf.ttl#>.
@prefix doap: <http://usefulinc.com/ns/doap#>.
@prefix earl: <http://www.w3.org/ns/earl#>.
@prefix foaf: <http://xmlns.com/foaf/0.1/>.
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix dc:   <http://purl.org/dc/elements/1.1/>.
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix software: <http://metacognition.info/software/> .
@prefix test: <http://www.w3.org/2009/sparql/docs/tests/data-sparql11/entailment/manifest#> .

myfoaf:chime a foaf:Person;
             foaf:homepage <http://metacognition.info>;
             foaf:name "Chimezie Ogbuji".

software:fuxi a doap:Project;
    doap:maintainer myfoaf:chime;
    doap:release [ a doap:Version; doap:name "1.4" ];
    foaf:homepage <http://code.google.com/p/fuxi/> ."""

test_graph = Graph().parse(StringIO(PERSON_AND_PROJECT),format='n3')

def GetTests():
    manifestGraph = Graph().parse(
        open('SPARQL/W3C/entailment/manifest.ttl'),
        format='n3')
    rt = manifestGraph.query(
                              MANIFEST_QUERY,
                              initNs=nsMap,
                              DEBUG = False)
    for test, name, queryFile, rdfDoc, regime, result in rt:
        if isinstance(regime,BNode):
            regime = list(Collection(manifestGraph,regime))
        else:
            regime = [regime]
        named_graph_query = MANIFEST_NAMED_GRAPHS_QUERY%(test.n3())
        named_graphs = list(manifestGraph.query(named_graph_query,initNs=nsMap))
        yield test.split(TEST)[-1], \
              name, \
              queryFile, \
              rdfDoc, \
              regime, \
              result,\
              named_graphs

def castToTerm(node):
    if node.xml_local == 'bnode':
        return BNode(u'')
    elif node.xml_local == 'uri':
        return URIRef(U(node))
    elif node.xml_local == 'literal':
        if node.xml_select('string(@datatype)'):
            dT = URIRef(U(node.xpath('string(@datatype)')))
            return Literal(U(node),datatype=dT)
        else:
            return Literal(U(node))
    else:
        raise NotImplementedError()

def parseResults(sparqlRT):
    from amara import bindery
    actualRT = []
    doc = bindery.parse(sparqlRT,
                        prefixes={
                            u'sparql':u'http://www.w3.org/2005/sparql-results#'})
    askAnswer=doc.xml_select('string(/sparql:sparql/sparql:boolean)')
    if askAnswer:
        askAnswer = U(askAnswer)
        actualRT=askAnswer==u'true'
    else:
        for result in doc.xml_select('/sparql:sparql/sparql:results/sparql:result'):
            currBind = {}
            for binding in result.binding:
                varVal = U(binding.name)
                var = Variable(varVal)
                term = castToTerm(binding.xml_select('*')[0])
                currBind[var]=term
            if currBind:
                actualRT.append(currBind)
    return actualRT
        
class TestSequence(unittest.TestCase):
    verbose = False
    def setUp(self):
        rule_store, rule_graph, self.network = SetupRuleStore(makeNetwork=True)
        self.network.nsMap = nsMap
        self.rdfs_rules=list(HornFromN3(open('SPARQL/W3C/rdf-rdfs.n3')))

def test_generator(testName, label, queryFile, rdfDoc, regime, result, named_graphs, debug):
    def test(self,debug=debug):
        if debug:
            print testName, label, named_graphs
        query     = urlopen(queryFile).read()
        try:
            parsedQuery=parse(query)
        except ParseException:
            return

        assertion     = BNode()
        result_node   = BNode()
        test_graph.add((result_node,RDF.type,EARL.TestResult))
        test_graph.add((result_node,DC['date'],Literal(datetime.date.today())))
        test_graph.add((assertion,RDF.type,EARL.Assertion))
        test_graph.add((assertion,EARL.assertedBy,MY_FOAF.chime))
        test_graph.add((assertion,
                        EARL.subject,
                        URIRef('http://metacognition.info/software/fuxi')))
        test_graph.add((assertion,EARL.test,TEST[testName]))
        test_graph.add((assertion,EARL.result,result_node))

        if named_graphs:
            g = ConjunctiveGraph()
        else:
            g = Graph()

        if debug:
            print "Source graph ", rdfDoc
        g.parse(
            urlopen(rdfDoc),
            publicID=rdfDoc,
            format='n3')

        for sourceUri, graphIri in named_graphs:
            g.parse(
                urlopen(sourceUri),
                publicID=graphIri,
                format='n3')
        if named_graphs:
            factGraph = Graph(g.store,identifier=rdfDoc)
        else:
            factGraph = g

        if ENT.RIF in regime:
            rules = []
        else:
            from FuXi.DLP.CompletionReasoning import GetELHConsequenceProcedureRules
            rules = [
                i for i in self.rdfs_rules
            ] if ENT.RDFS in regime else []
            rules.extend(self.network.setupDescriptionLogicProgramming(
                                                         factGraph,
                                                         addPDSemantics=True,
                                                         constructNetwork=False))
            if query.find('subClassOf')+1 and (
                ENT.RDFS not in regime or
                testName in COMPLETION_RULES
                ):
                if debug:
                    print "Added completion rules for EL TBox reasoning"
                rules.extend(GetELHConsequenceProcedureRules(factGraph))
                facts2add = []
                for owl_class in factGraph.subjects(RDF.type,OWLNS.Class):
                    facts2add.append(
                        (owl_class,RDFS.subClassOf,owl_class,factGraph)
                    )
                factGraph.addN(facts2add)
            if debug:
                pprint(list(rules))
        if debug:
            print query
        topDownStore=TopDownSPARQLEntailingStore(
                        factGraph.store,
                        factGraph,
                        idb=rules,
                        DEBUG=debug,
                        nsBindings=nsMap,
                        #hybridPredicates = [RDFS.subClassOf],
                        identifyHybridPredicates = True,
                        templateMap={
                            STRING.contains : "REGEX(%s,%s)"
                        })
        targetGraph = Graph(topDownStore)
        for pref,nsUri in (setdict(nsMap) | setdict(
                parsedQuery.prolog.prefixBindings)).items():
            targetGraph.bind(pref,nsUri)
        rt=targetGraph.query('',parsedQuery=parsedQuery)
        if rt.askAnswer:
            actualSolns   = rt.askAnswer[0]
            expectedSolns = parseResults(urlopen(result).read())
        else:
            actualSolns=[ImmutableDict([(k,v)
                            for k,v in d.items()])
                                for d in parseResults(rt.serialize(format='xml'))]
            expectedSolns=[ImmutableDict([(k,v)
                            for k,v in d.items()])
                                for d in parseResults(urlopen(result).read())]
            actualSolns.sort(key=lambda d:hash(d))
            expectedSolns.sort(key=lambda d:hash(d))

            actualSolns   = set(actualSolns)
            expectedSolns = set(expectedSolns)

        if actualSolns == expectedSolns:
            test_graph.add((result_node,EARL.outcome,EARL['pass']))
        else:
            test_graph.add((result_node,EARL.outcome,EARL['fail']))
        self.failUnless(actualSolns == expectedSolns,
                        "Answers don't match %s v.s. %s"%(actualSolns,
                                                          expectedSolns)
        )
        if debug:
            for network,goal in topDownStore.queryNetworks:
                pprint(goal)
                network.reportConflictSet(True)
    return test

if __name__ == '__main__':
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
    op.add_option('--profile',
                  action='store_true',
                  default=False,
      help = 'Whether or not to run a profile')
    op.add_option('--singleTest',
      help = 'The short name of the test to run')
    op.add_option('--debug','-v',
                  action='store_true',
                  default=False,
      help = 'Run the test in verbose mode')
    (options, facts) = op.parse_args()
    for test, name, queryFile, rdfDoc, regime, result, named_graphs in GetTests():
        if test in SKIP or options.singleTest is not None and options.singleTest != test:
            if test in SKIP and options.debug:
                print "\tSkipping (%s)"%test,SKIP[test]#>>sys.stderr,SKIP[test],
        elif set(regime).intersection(SUPPORTED_ENTAILMENT):
            test_name = 'test_%s' % test
            test = test_generator(
                        test,
                        name,
                        queryFile,
                        rdfDoc,
                        regime,
                        result,
                        named_graphs,
                        options.debug)
            setattr(TestSequence, test_name, test)
    if options.profile:
        from hotshot import Profile, stats
        p = Profile('fuxi.profile')
        p.runcall(unittest.TextTestRunner(verbosity=5).run,
                  unittest.makeSuite(TestSequence))
        p.close()
        s = stats.load('fuxi.profile')
        s.strip_dirs()
        s.sort_stats('time','cumulative','pcalls')
        s.print_stats(.1)
        s.print_callers(.05)
        s.print_callees(.05)
    else:
        unittest.TextTestRunner(verbosity=5).run(
            unittest.makeSuite(TestSequence)
        )
    if not options.debug:
        print test_graph.serialize(format='n3')