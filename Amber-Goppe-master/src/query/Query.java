package query;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

import org.apache.jena.graph.Node;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.Syntax;
import org.apache.jena.sparql.core.TriplePath;
import org.apache.jena.sparql.core.Var;
import org.apache.jena.sparql.path.P_Alt;
import org.apache.jena.sparql.path.P_Distinct;
import org.apache.jena.sparql.path.P_FixedLength;
import org.apache.jena.sparql.path.P_Inverse;
import org.apache.jena.sparql.path.P_Link;
import org.apache.jena.sparql.path.P_Mod;
import org.apache.jena.sparql.path.P_Multi;
import org.apache.jena.sparql.path.P_NegPropSet;
import org.apache.jena.sparql.path.P_OneOrMore1;
import org.apache.jena.sparql.path.P_OneOrMoreN;
import org.apache.jena.sparql.path.P_ReverseLink;
import org.apache.jena.sparql.path.P_Seq;
import org.apache.jena.sparql.path.P_Shortest;
import org.apache.jena.sparql.path.P_ZeroOrMore1;
import org.apache.jena.sparql.path.P_ZeroOrMoreN;
import org.apache.jena.sparql.path.P_ZeroOrOne;
import org.apache.jena.sparql.path.Path;
import org.apache.jena.sparql.path.PathVisitor;
import org.apache.jena.sparql.syntax.ElementPathBlock;
import org.apache.jena.sparql.syntax.ElementVisitorBase;
import org.apache.jena.sparql.syntax.ElementWalker;
import org.khelekore.prtree.SimplePointND;

import com.gs.collections.api.iterator.MutableIntIterator;
import com.gs.collections.api.iterator.MutableShortIterator;
import com.gs.collections.api.set.primitive.MutableIntSet;
import com.gs.collections.impl.list.mutable.primitive.IntArrayList;
import com.gs.collections.impl.map.mutable.primitive.IntObjectHashMap;
import com.gs.collections.impl.map.mutable.primitive.ObjectIntHashMap;
import com.gs.collections.impl.map.mutable.primitive.ShortIntHashMap;
import com.gs.collections.impl.set.mutable.primitive.IntHashSet;
import com.gs.collections.impl.set.mutable.primitive.ShortHashSet;

import data.GoppeGraphDatabase;
import data.GraphDatabase;
import data.Settings;
import dk.brics.automaton.Automaton;
import dk.brics.automaton.RegExp;
import propertypaths.GraphAutomaton;
import propertypaths.Inverser;
import propertypaths.OPERATOR;
import propertypaths.PPSolver;
import propertypaths.PairInt;
import propertypaths.QueryTree;
import propertypaths.StateNode;
import propertypaths.TreeLeaf;
import propertypaths.TreeNode;

public class Query {

	/**
	 * A HashMap Int -> Set. Given a node id x, returns the set of query nodes y
	 * with y -> x.
	 */
	private IntObjectHashMap<IntHashSet> in_list;

	/**
	 * A HashMap Int -> Set. Given a node id x, returns the set of query nodes y
	 * with x -> y.
	 */
	private IntObjectHashMap<IntHashSet> out_list;
	/**
	 * Given a {@link Pair} a query nodes (x,y), returns the predicates (short
	 * numbers) linking them.
	 */
	private HashMap<Pair, ShortHashSet> pair2dims;
	private HashMap<Pair, short[]> pair2dims_vec;

	/**
	 * ArrayList of projection variables.
	 */
	private ArrayList<String> headerList;
	private IntObjectHashMap<String> id2token;
	private ObjectIntHashMap<String> token2id;
	private IntObjectHashMap<ShortHashSet> selfLoop;
	public IntObjectHashMap<Integer> notVariable;
	private ShortIntHashMap dim_stat;
	private GraphDatabase g;
	IntObjectHashMap<IntHashSet> cores2sats; // Link every core to its
												// satellites
	public IntObjectHashMap<IntHashSet> possible_candidates = new IntObjectHashMap<IntHashSet>();
	private Vector<ObjectPath> path;

	private LinkedList<int[]> results;

	// Property paths attributes
	private int pathLength;
	private boolean hasPropertyPath;
	private String processedQuery;
	private IntArrayList projection;
	private HashMap<Pair, ArrayList<QueryTree>> pair2ast; // HashMap (x,y) ->
															// ast
	private IntObjectHashMap<ArrayList<QueryTree>> selfLoopPP;
	private TreeSet<Integer> normalLinkNodes;
	private TreeSet<Integer> ppLinkNodes;

	private int countPP = 0;
	private int countTriples = 0;
	private boolean allPP = false;

	public Query(GraphDatabase g, String queryFile) {
		in_list = new IntObjectHashMap<IntHashSet>();
		out_list = new IntObjectHashMap<IntHashSet>();
		pair2dims = new HashMap<Pair, ShortHashSet>();
		pair2dims_vec = new HashMap<Pair, short[]>();
		headerList = new ArrayList<String>();
		id2token = new IntObjectHashMap<String>();
		token2id = new ObjectIntHashMap<String>();
		selfLoop = new IntObjectHashMap<ShortHashSet>();
		notVariable = new IntObjectHashMap<Integer>();
		dim_stat = g.getPredicates_occurrences();
		this.g = g;
		cores2sats = new IntObjectHashMap<IntHashSet>();
		path = new Vector<ObjectPath>();

		pathLength = 0;
		hasPropertyPath = false;
		pair2ast = new HashMap<>();
		selfLoopPP = new IntObjectHashMap<>();
		normalLinkNodes = new TreeSet<Integer>();
		ppLinkNodes = new TreeSet<Integer>();

		String queryString = "";
		try {
			queryString = readFile(queryFile, Charset.forName("UTF-8"));
		} catch (IOException e) {
			System.err.println("Error while reading query file.");
		}
		// First parsing of the query
		org.apache.jena.query.Query q = QueryFactory.create(queryString, Syntax.syntaxARQ);

		// Projection variables
		for (Var p : q.getProjectVars()) {
			addSelect(p.toString());
		}

		// System.out.println(q.getProjectVars());
		processedQuery = "SELECT ";
		if (q.isDistinct())
			processedQuery += "DISTINCT ";
		for (Var i : q.getProjectVars()) {
			processedQuery += i.toString() + " ";
		}
		processedQuery += " WHERE {";

		// We reconstruct the query with the inverse of the PPs to make sure
		// that we parse pps with the inverse symbol stuck with atoms

		ElementWalker.walk(q.getQueryPattern(),
				// For each element...
				new ElementVisitorBase() {
					// ...when it's a block of triples...
					public void visit(ElementPathBlock el) {
						// ...go through all the triples...
						Iterator<TriplePath> triples = el.patternElts();
						while (triples.hasNext()) {
							TriplePath t = triples.next();
							Path path = t.getPath();
							Node sub = t.getSubject();
							String subString = sub.toString();
							if (!sub.isVariable())
								subString = "<" + subString + ">";

							Node obj = t.getObject();
							String objString = obj.toString();
							if (!obj.isVariable())
								objString = "<" + objString + ">";

							// System.out.println(path.toString());
							processedQuery += subString + " " + new Inverser(path.toString()).getInversed() + " "
									+ objString + " . ";
							// System.out.println("processed : " +
							// processedQuery);

						}
					}
				});
		processedQuery += "}";

		// System.out.println("PROCESSED QUERY :\n" + processedQuery);
		// System.out.println("===============");
		q = QueryFactory.create(processedQuery, Syntax.syntaxARQ);

		// Now that we inversed every property path, we need to construct the
		// Query object wrt to each triple
		ElementWalker.walk(q.getQueryPattern(), new ElementVisitorBase() {
			public void visit(ElementPathBlock el) {
				ListIterator<TriplePath> it = el.getPattern().iterator();
				while (it.hasNext()) {
					final TriplePath tp = it.next();
					countTriples += 1;
					hasPropertyPath = detectPropertyPaths(tp);
					QueryTree pp = null;
					if (hasPropertyPath) {
						countPP += 1;
						pp = parsePropertyPath(tp);
					}
					Node subject = tp.getSubject();
					Node object = tp.getObject();
					Node predicate = tp.getPredicate();
					int subjectVariable = -1;
					int objectVariable = -1;
					String s = subject.toString();
					String o = object.toString();
					if (!subject.isVariable()) {
						s = "<" + s + ">";
						subjectVariable = 0;
					}
					if (!object.isVariable()) {
						o = "<" + o + ">";
						objectVariable = 0;
					}

					short pred = (short) GoppeGraphDatabase.getDatabase().getString2ShortP().get("<" + predicate + ">");
					// Adds (s,pred,o) as triple, with -1 meaning that there
					// are variables
					addTriple(s, o, pred, subjectVariable, objectVariable, pp);

				}
			}
		});
		if (countPP == countTriples) {
			setAllPP(true);
		}
		// Long end = System.nanoTime();
		// System.out.println("query parsing time: " + (end - start));
		path = getQueryStructure(); // query spanning tree
		// System.out.println("====");

		// Print each ObjectPath information
		// for (ObjectPath s : path)
		// System.out.println(s);

		projection = selectVariableProjection();
		// System.out.println("compute query structure and ordering time: " +
		// (end - start));
		results = new LinkedList<int[]>();
	}

	public QueryTree parsePropertyPath(TriplePath t) {
		QueryTree ast = new QueryTree();
		Path path = t.getPath();
		Node sub = t.getSubject();
		Node obj = t.getObject();

		// To compute synopsis for query nodes with a property path,
		// computes all outgoing labels from the automaton of the whole property
		// path, used for candidates computation.
		PPSolver solv = new PPSolver(path.toString());
		RegExp r = new RegExp(solv.getRegex());
		Automaton a = r.toAutomaton();
		a.determinize();
		GraphAutomaton ga = new GraphAutomaton(a);
		ast.setOriginalAutomaton(ga);
		ast.setInitialPP(path.toString());

		for (Integer l : ga.getInitialState().getOutLabels()) {
			String p = GoppeGraphDatabase.getDatabase().convertIntToStringP(l);
			short m = (short) GoppeGraphDatabase.getDatabase().getString2ShortP().get(p);
			ast.addStartLabel(m); // ast contains already converted shorts
		}

		//

		if (!sub.isVariable()) {
			ast.setFixedLeft();
			int convertedURI = GoppeGraphDatabase.getDatabase().convertStringToIntSO("<" + sub.getURI() + ">");
			ast.setFixedStart(convertedURI);
		}
		if (!obj.isVariable()) {
			System.err.println("Can't start with fixed node right.");
			return null;
		}

		path.visit(new PathVisitor() {

			@Override
			public void visit(P_Seq arg0) {

				TreeNode n = new TreeNode(OPERATOR.SEQ, arg0.getLeft().toString(), arg0.getRight().toString(), ast);
				ast.add(n);
				arg0.getLeft().visit(this);
				arg0.getRight().visit(this);
			}

			@Override
			public void visit(P_Alt arg0) {

				TreeNode n = new TreeNode(OPERATOR.ALT, arg0.getLeft().toString(), arg0.getRight().toString(), ast);
				ast.add(n);

				arg0.getLeft().visit(this);
				arg0.getRight().visit(this);
			}

			@Override
			public void visit(P_OneOrMoreN arg0) {

				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_OneOrMore1 arg0) {
				TreeLeaf l = new TreeLeaf(OPERATOR.OneOrMore, arg0.toString(), ast);
				ast.add(l);
			}

			@Override
			public void visit(P_ZeroOrMoreN arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_ZeroOrMore1 arg0) {
				TreeLeaf l = new TreeLeaf(OPERATOR.ZeroOrMore, arg0.toString(), ast);
				ast.add(l);
			}

			@Override
			public void visit(P_ZeroOrOne arg0) {

				TreeLeaf l = new TreeLeaf(OPERATOR.ZeroOrOne, arg0.toString(), ast);
				ast.add(l);
			}

			@Override
			public void visit(P_Shortest arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Multi arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Distinct arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_FixedLength arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Mod arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Inverse arg0) {
				// System.out.println("On a un inverse : " + arg0.toString());
				TreeNode n = new TreeNode(OPERATOR.INV, arg0.getSubPath().toString(), null, ast);
				ast.add(n);
				arg0.getSubPath().visit(this);
			}

			@Override
			public void visit(P_NegPropSet arg0) {
				// String sub = arg0.toString().substring(1,
				// arg0.toString().length());
				// System.out.println("sub : " + sub);

				TreeLeaf l = new TreeLeaf(OPERATOR.NEG, arg0.toString(), ast);
				ast.add(l);
			}

			@Override
			public void visit(P_ReverseLink arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);

			}

			@Override
			public void visit(P_Link arg0) {
				TreeLeaf l = new TreeLeaf(OPERATOR.Link, arg0.toString(), ast);
				ast.add(l);

			}
		});
		return ast;
	}

	/**
	 * Returns true if the current triple is a property path.
	 * 
	 * @param tp
	 * @return true if the current triple contains a property path, false
	 *         otherwise.
	 */
	protected boolean detectPropertyPaths(TriplePath tp) {
		pathLength = 0;
		tp.getPath().visit(new PathVisitor() {
			@Override
			public void visit(P_Seq arg0) {
				pathLength++;
				arg0.getLeft().visit(this);
				arg0.getRight().visit(this);
			}

			@Override
			public void visit(P_Alt arg0) {
				pathLength++;
				arg0.getLeft().visit(this);
				arg0.getRight().visit(this);
			}

			@Override
			public void visit(P_OneOrMoreN arg0) {

				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_OneOrMore1 arg0) {
				pathLength++;
			}

			@Override
			public void visit(P_ZeroOrMoreN arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_ZeroOrMore1 arg0) {
				pathLength++;
			}

			@Override
			public void visit(P_ZeroOrOne arg0) {
				pathLength++;
			}

			@Override
			public void visit(P_Shortest arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Multi arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Distinct arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_FixedLength arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Mod arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);
			}

			@Override
			public void visit(P_Inverse arg0) {
				pathLength++;
				arg0.getSubPath().visit(this);
			}

			@Override
			public void visit(P_NegPropSet arg0) {
				pathLength++;
			}

			@Override
			public void visit(P_ReverseLink arg0) {
				System.err.println(
						"Can't read this type of property path. (" + arg0.getClass().getName() + ")" + "\n\t" + arg0);
				System.exit(1);

			}

			@Override
			public void visit(P_Link arg0) {

			}
		});
		return pathLength > 0;
	}

	public void decompose() {
		MutableIntSet node_set = id2token.keySet();
		MutableIntIterator itr = node_set.intIterator();
		IntHashSet satellites = new IntHashSet();
		IntHashSet cores = new IntHashSet();
		// Gathering core nodes (> 1 neighbors)
		// and satellite nodes
		while (itr.hasNext()) {
			int node_id = itr.next();
			IntHashSet temp_neighs = new IntHashSet();
			if (in_list.containsKey(node_id))
				temp_neighs.addAll(in_list.get(node_id));
			if (out_list.containsKey(node_id))
				temp_neighs.addAll(out_list.get(node_id));

			if (temp_neighs.size() == 1) {
				// System.out.println(id2token.get(node_id) + " (" + node_id +
				// ") is a satellite.");
				satellites.add(node_id);
			} else {
				// System.out.println(id2token.get(node_id) + " (" + node_id +
				// ") is a core.");
				cores.add(node_id);
			}
		}

		// Case of single triple query, set one of the nodes to a core and the
		// other one to a satellite.
		if (cores.size() == 0 && satellites.size() == 2) {
			int[] sats = satellites.toSortedArray();
			satellites.clear();
			cores.add(sats[0]);
			satellites.add(sats[1]);
		}

		// Matching cores and their satellites
		itr = cores.intIterator();
		while (itr.hasNext()) {
			int core_id = itr.next();
			cores2sats.put(core_id, new IntHashSet());
			MutableIntIterator itr1 = satellites.intIterator();
			while (itr1.hasNext()) {
				int sat_id = itr1.next();
				if (in_list.containsKey(core_id) && in_list.get(core_id).contains(sat_id)) {
					cores2sats.get(core_id).add(sat_id);
				}
				if (out_list.containsKey(core_id) && out_list.get(core_id).contains(sat_id)) {
					cores2sats.get(core_id).add(sat_id);
				}
			}
		}
	}

	/* HEURISTICS TO ORDER THE QUERY NODES FROM THE SECOND TO THE LAST */
	public IntHashSet chooseMoreSelective(IntHashSet already_considered, IntHashSet ranked_tie_connecitvity) {
		MutableIntIterator itr_not_yet_ranked = ranked_tie_connecitvity.intIterator();
		int best_min_dims = Integer.MAX_VALUE;

		IntObjectHashMap<IntHashSet> prop2node = new IntObjectHashMap<IntHashSet>();

		while (itr_not_yet_ranked.hasNext()) {
			int not_yet_ranked = itr_not_yet_ranked.next();
			int min_dims = Integer.MAX_VALUE;
			MutableIntIterator itr_already = already_considered.intIterator();
			while (itr_already.hasNext()) {
				int yet_ordered = itr_already.next();
				if (in_list.containsKey(not_yet_ranked) && in_list.get(not_yet_ranked).contains(yet_ordered)) {
					if (pair2dims.get(new Pair(yet_ordered, not_yet_ranked)) != null) {
						MutableShortIterator itrs = pair2dims.get(new Pair(yet_ordered, not_yet_ranked))
								.shortIterator();
						while (itrs.hasNext()) {
							min_dims = Math.min(min_dims, dim_stat.get(itrs.next()));
						}
					}
					if (pair2ast.get(new Pair(yet_ordered, not_yet_ranked)) != null) {
						ArrayList<QueryTree> p = pair2ast.get(new Pair(yet_ordered, not_yet_ranked));
						for (QueryTree qt : p) {
							ArrayList<StateNode> finalStates = qt.getOriginalAutomaton().getFinalStates();
							for (StateNode f : finalStates) {
								for (int l : f.getInLabels()) {
									String predS = GoppeGraphDatabase.getDatabase().convertIntToStringP(l);
									short pred = (short) GoppeGraphDatabase.getDatabase().getString2ShortP().get(predS);
									min_dims = Math.min(min_dims, dim_stat.get(pred));
								}
							}
						}
					}
				}

				if (out_list.containsKey(not_yet_ranked) && out_list.get(not_yet_ranked).contains(yet_ordered)) {
					if (pair2dims.get(new Pair(not_yet_ranked, yet_ordered)) != null) {
						MutableShortIterator itrs = pair2dims.get(new Pair(not_yet_ranked, yet_ordered))
								.shortIterator();
						while (itrs.hasNext()) {
							min_dims = Math.min(min_dims, dim_stat.get(itrs.next()));
						}
					}
					if (pair2ast.get(new Pair(not_yet_ranked, yet_ordered)) != null) {
						ArrayList<QueryTree> p = pair2ast.get(new Pair(not_yet_ranked, yet_ordered));
						for (QueryTree qt : p) {
							StateNode f = qt.getOriginalAutomaton().getInitialState();
							for (int l : f.getInLabels()) {
								String predS = GoppeGraphDatabase.getDatabase().convertIntToStringP(l);
								short pred = (short) GoppeGraphDatabase.getDatabase().getString2ShortP().get(predS);
								min_dims = Math.min(min_dims, dim_stat.get(pred));
							}

						}
					}
				}
			}
			if (!prop2node.containsKey(min_dims))
				prop2node.put(min_dims, new IntHashSet());
			prop2node.get(min_dims).add(not_yet_ranked);

			if (min_dims < best_min_dims)
				best_min_dims = min_dims;
		}
		return prop2node.get(best_min_dims);
	}

	public IntHashSet chooseMoreNovelCoverage(IntHashSet already_considered, IntHashSet not_yet_consider) {
		// System.out.println(not_yet_consider.size());
		MutableIntIterator itr_not_yet = not_yet_consider.intIterator();
		int max_links = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();

		MutableIntIterator itr_already = already_considered.intIterator();
		IntHashSet frontier = new IntHashSet();

		while (itr_already.hasNext()) {
			int yet_ordered = itr_already.next();
			if (in_list.containsKey(yet_ordered))
				frontier.addAll(in_list.get(yet_ordered));

			if (out_list.containsKey(yet_ordered))
				frontier.addAll(out_list.get(yet_ordered));
		}

		while (itr_not_yet.hasNext()) {
			int not_yet_ordered = itr_not_yet.next();
			IntHashSet not_yet_ordered_frontier = new IntHashSet();
			if (in_list.containsKey(not_yet_ordered))
				not_yet_ordered_frontier.addAll(in_list.get(not_yet_ordered));

			if (out_list.containsKey(not_yet_ordered))
				not_yet_ordered_frontier.addAll(out_list.get(not_yet_ordered));

			not_yet_ordered_frontier.retainAll(frontier);

			if (!nlinks2node.containsKey(not_yet_ordered_frontier.size()))
				nlinks2node.put(not_yet_ordered_frontier.size(), new IntHashSet());

			nlinks2node.get(not_yet_ordered_frontier.size()).add(not_yet_ordered);
			if (not_yet_ordered_frontier.size() > max_links)
				max_links = not_yet_ordered_frontier.size();
		}

		return nlinks2node.get(max_links);

	}

	public IntHashSet connectivityTopRanked(IntHashSet already_considered, IntHashSet not_yet_consider) {
		MutableIntIterator itr_not_yet = not_yet_consider.intIterator();
		int max_links = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();

		while (itr_not_yet.hasNext()) {
			int not_yet_ordered = itr_not_yet.next();
			int count_links = 0;
			MutableIntIterator itr_already = already_considered.intIterator();
			while (itr_already.hasNext()) {
				int yet_ordered = itr_already.next();
				// if current not ordered yet core has a link by a
				// already ordered core, increments by the number of predicates
				// linking to it.
				if (in_list.containsKey(not_yet_ordered) && in_list.get(not_yet_ordered).contains(yet_ordered)) {
					if (pair2dims.get(new Pair(yet_ordered, not_yet_ordered)) != null)
						count_links += pair2dims.get(new Pair(yet_ordered, not_yet_ordered)).size();
					if (pair2ast.get(new Pair(yet_ordered, not_yet_ordered)) != null)
						count_links += pair2ast.get(new Pair(yet_ordered, not_yet_ordered)).size();
				}
				if (out_list.containsKey(not_yet_ordered) && out_list.get(not_yet_ordered).contains(yet_ordered)) {
					if (pair2dims.get(new Pair(not_yet_ordered, yet_ordered)) != null)
						count_links += pair2dims.get(new Pair(not_yet_ordered, yet_ordered)).size();
					if (pair2ast.get(new Pair(not_yet_ordered, yet_ordered)) != null)
						count_links += pair2ast.get(new Pair(not_yet_ordered, yet_ordered)).size();
				}
			}
			if (!nlinks2node.containsKey(count_links))
				nlinks2node.put(count_links, new IntHashSet());

			nlinks2node.get(count_links).add(not_yet_ordered);
			if (count_links > max_links)
				max_links = count_links;
		}

		return nlinks2node.get(max_links);

	}

	public IntHashSet connectivityTopRanked2Hop(IntHashSet already_considered, IntHashSet not_yet_consider) {
		MutableIntIterator itr_not_yet = not_yet_consider.intIterator();
		int max_links = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();

		while (itr_not_yet.hasNext()) {
			int not_yet_ordered = itr_not_yet.next();
			int count_links = 0;

			if (in_list.containsKey(not_yet_ordered)) {
				MutableIntIterator itr_in_neighs_nod = in_list.get(not_yet_ordered).intIterator();
				MutableIntIterator itr_already = already_considered.intIterator();
				while (itr_already.hasNext()) {
					int yet_ordered = itr_already.next();
					while (itr_in_neighs_nod.hasNext()) {
						int in_neigh = itr_in_neighs_nod.next();
						if (in_list.containsKey(in_neigh) && in_list.get(in_neigh).contains(yet_ordered)) {
							if (pair2dims.get(new Pair(in_neigh, not_yet_ordered)) != null)
								count_links += pair2dims.get(new Pair(in_neigh, not_yet_ordered)).size();
							if (pair2ast.get(new Pair(in_neigh, not_yet_ordered)) != null)
								count_links += pair2ast.get(new Pair(in_neigh, not_yet_ordered)).size();
						}
						if (out_list.containsKey(in_neigh) && out_list.get(in_neigh).contains(yet_ordered)) {
							if (pair2dims.get(new Pair(in_neigh, yet_ordered)) != null)
								count_links += pair2dims.get(new Pair(in_neigh, yet_ordered)).size();
							if (pair2ast.get(new Pair(in_neigh, yet_ordered)) != null)
								count_links += pair2ast.get(new Pair(in_neigh, yet_ordered)).size();
						}
					}
				}
			}

			if (out_list.containsKey(not_yet_ordered)) {
				MutableIntIterator itr_out_neighs_nod = out_list.get(not_yet_ordered).intIterator();
				MutableIntIterator itr_already = already_considered.intIterator();
				while (itr_already.hasNext()) {
					int yet_ordered = itr_already.next();
					while (itr_out_neighs_nod.hasNext()) {
						int out_neigh = itr_out_neighs_nod.next();
						if (in_list.containsKey(out_neigh) && in_list.get(out_neigh).contains(yet_ordered)) {
							if (pair2dims.get(new Pair(out_neigh, not_yet_ordered)) != null)
								count_links += pair2dims.get(new Pair(out_neigh, not_yet_ordered)).size();
							if (pair2ast.get(new Pair(out_neigh, not_yet_ordered)) != null)
								count_links += pair2dims.get(new Pair(out_neigh, not_yet_ordered)).size();
						}
						if (out_list.containsKey(out_neigh) && out_list.get(out_neigh).contains(yet_ordered)) {
							if (pair2dims.get(new Pair(out_neigh, yet_ordered)) != null)
								count_links += pair2dims.get(new Pair(out_neigh, yet_ordered)).size();
							if (pair2ast.get(new Pair(out_neigh, yet_ordered)) != null)
								count_links += pair2ast.get(new Pair(out_neigh, yet_ordered)).size();

						}
					}
				}

			}
			if (!nlinks2node.containsKey(count_links))
				nlinks2node.put(count_links, new IntHashSet());

			nlinks2node.get(count_links).add(not_yet_ordered);
			if (count_links > max_links)
				max_links = count_links;

		}

		return nlinks2node.get(max_links);

	}

	public IntHashSet chooseMaxSatNodes(IntHashSet already_considered, IntHashSet not_yet_consider) {
		MutableIntIterator itr_not_yet = not_yet_consider.intIterator();
		int max_links = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();

		while (itr_not_yet.hasNext()) {
			int not_yet_ordered = itr_not_yet.next();
			int count_links = 0;
			MutableIntIterator itr_already = already_considered.intIterator();
			while (itr_already.hasNext()) {
				int yet_ordered = itr_already.next();
				if (in_list.containsKey(not_yet_ordered) && in_list.get(not_yet_ordered).contains(yet_ordered))
					count_links = Math.max(count_links, cores2sats.get(not_yet_ordered).size());

				if (out_list.containsKey(not_yet_ordered) && out_list.get(not_yet_ordered).contains(yet_ordered))
					count_links = Math.max(count_links, cores2sats.get(not_yet_ordered).size());
			}
			if (!nlinks2node.containsKey(count_links))
				nlinks2node.put(count_links, new IntHashSet());

			nlinks2node.get(count_links).add(not_yet_ordered);
			if (count_links > max_links)
				max_links = count_links;
		}
		return nlinks2node.get(max_links);

	}

	/* HEURISTICS TO ORDER THE FIRST QUERY NODE */
	public IntHashSet chooseMaxLiteralorURI(MutableIntSet core_set) {
		int max_links_literal_uri = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();
		MutableIntIterator itr = core_set.intIterator();
		while (itr.hasNext()) {
			int node_id = itr.next();
			int current_links = 0;
			if (in_list.containsKey(node_id)) {
				MutableIntIterator it1 = in_list.get(node_id).intIterator();
				while (it1.hasNext()) {
					if (notVariable.containsKey(it1.next())) {
						current_links++;
					}
				}
			}
			if (out_list.containsKey(node_id)) {
				MutableIntIterator it1 = out_list.get(node_id).intIterator();
				while (it1.hasNext()) {
					if (notVariable.containsKey(it1.next())) {
						current_links++;
					}
				}
			}

			if (!nlinks2node.containsKey(current_links))
				nlinks2node.put(current_links, new IntHashSet());

			nlinks2node.get(current_links).add(node_id);

			if (current_links > max_links_literal_uri)
				max_links_literal_uri = current_links;
		}
		return nlinks2node.get(max_links_literal_uri);
	}

	public IntHashSet chooseMaxLinks(MutableIntSet core_set) {
		int max_links = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();
		MutableIntIterator itr = core_set.intIterator();
		while (itr.hasNext()) {
			int node_id = itr.next();
			int current_links = 0;
			if (in_list.containsKey(node_id)) {
				current_links += in_list.get(node_id).size();
			}
			if (out_list.containsKey(node_id)) {
				current_links += out_list.get(node_id).size();
			}
			if (!nlinks2node.containsKey(current_links))
				nlinks2node.put(current_links, new IntHashSet());

			nlinks2node.get(current_links).add(node_id);
			if (current_links > max_links)
				max_links = current_links;
		}
		// System.out.println("maxLinks : " + nlinks2node.get(max_links));
		return nlinks2node.get(max_links);

	}

	/**
	 * Gets the core node having the greatest number of satellites.
	 * 
	 * @param core_set
	 * @return
	 */
	public IntHashSet chooseMaxSatNodes(MutableIntSet core_set) {
		int max_links = 0;
		IntObjectHashMap<IntHashSet> nlinks2node = new IntObjectHashMap<IntHashSet>();
		MutableIntIterator itr = core_set.intIterator();
		while (itr.hasNext()) {
			int node_id = itr.next();
			int current_links = cores2sats.get(node_id).size();
			if (current_links > max_links)
				max_links = current_links;
			if (!nlinks2node.containsKey(current_links))
				nlinks2node.put(current_links, new IntHashSet());

			nlinks2node.get(current_links).add(node_id);
		}
		// System.out.println("MaxSatNodes : " + nlinks2node.get(max_links));
		return nlinks2node.get(max_links);

	}

	public boolean existNormalLink(int node) {
		return normalLinkNodes.contains(node);
	}

	public boolean existPPLink(int node) {
		return ppLinkNodes.contains(node);
	}

	/**
	 * Given a query node (@link {@link ObjectPath}'s id, computes candidates
	 * with Goppe for each property path link, in and out, and does the
	 * intersection.
	 * 
	 * @param node
	 * @return
	 */
	public IntHashSet getCandidatePP(int node) {
		// System.out.println("GETTING PP CANDIDATES FOR NODE : " +
		// id2token.get(node));
		// for each PP arcs of the current node
		IntHashSet candidates = new IntHashSet();

		// Handling property paths outgoing
		IntHashSet out = out_list.get(node);
		if (out != null) {
			MutableIntIterator it = out.intIterator();
			while (it.hasNext()) {
				int o = it.next();
				Pair pairToCheck = new Pair(node, o);
				if (pair2ast.containsKey(pairToCheck)) {
					ArrayList<QueryTree> pps = pair2ast.get(pairToCheck);
					IntHashSet temp_c = new IntHashSet();
					ArrayList<Integer> c = GoppeGraphDatabase.getDatabase()
							.computeFrontCandidates(pps.get(0).getOriginalAutomaton());
					for (Integer can : c) {
						temp_c.add(can);
					}
					candidates.addAll(temp_c);
					for (int i = 1; i < pps.size(); i++) {
						temp_c = new IntHashSet();
						c = GoppeGraphDatabase.getDatabase().computeFrontCandidates(pps.get(i).getOriginalAutomaton());
						for (Integer can : c) {
							temp_c.add(can);
						}
						candidates.retainAll(temp_c);
					}
				}
			}
		}
		// System.out.println("> Candidates pp only out : " + candidates);
		IntHashSet in_can = new IntHashSet();
		// Handling pp incoming
		IntHashSet in = in_list.get(node);
		if (in != null) {
			MutableIntIterator it = in.intIterator();
			while (it.hasNext()) {
				int o = it.next();
				Pair pairToCheck = new Pair(o, node);
				if (pair2ast.containsKey(pairToCheck)) {
					ArrayList<QueryTree> pps = pair2ast.get(pairToCheck);
					IntHashSet temp_c = new IntHashSet();
					ArrayList<PairInt> c = GoppeGraphDatabase.getDatabase()
							.computeBackCandidates(pps.get(0).getOriginalAutomaton());
					// Bugged back candidates ?
					for (PairInt can : c) {
						temp_c.add(can.getRight());
					}
					in_can.addAll(temp_c);
					for (int i = 1; i < pps.size(); i++) {
						temp_c = new IntHashSet();
						c = GoppeGraphDatabase.getDatabase().computeBackCandidates(pps.get(i).getOriginalAutomaton());
						for (PairInt can : c) {
							temp_c.add(can.getRight());
						}
						in_can.retainAll(temp_c);
					}
				}
			}
		}
		// System.out.println("> Candidates pp only in : " + in_can);

		if (in_can.size() > 0 && candidates.size() > 0) {
			candidates.retainAll(in_can);
		} else if (in_can.size() > 0 && candidates.size() == 0) {
			candidates.addAll(in_can);
		}

		// System.out.println("Candidates pp for node " + node + " : " +
		// candidates);
		return candidates;
	}

	public int[] getOrdering() {
		int[] ordering = new int[cores2sats.size()];
		MutableIntSet core_set = cores2sats.keySet();
		MutableIntIterator itr = core_set.intIterator();
		int max_id = -1;
		boolean no_sol = false;
		// For each core node
		while (itr.hasNext()) {
			int node_id = itr.next();
			int counter = 0;
			if (notVariable.containsKey(node_id)) {
				counter = 1;
				IntHashSet temp = new IntHashSet();
				temp.add(notVariable.get(node_id));
				possible_candidates.put(node_id, temp);
			} else {
				IntHashSet retrieved_vertices = new IntHashSet();
				IntHashSet pp_possible_initial_matches = new IntHashSet();
				// System.out.println("Syn : " + g.getCompacted_synopsis());
				if (existNormalLink(node_id)) {
					// System.out.println("Getting neighbhors without
					// considering pp : ");
					SimplePointND query_r_tree = getSynopsis(node_id);
					IntHashSet v = g.getNodeList(query_r_tree);
					// System.out.println("getNodeList(" + node_id + ") : " +
					// v);
					retrieved_vertices.addAll(v);
					// System.out.println("Normal candidates for node : " +
					// node_id + " : " + retrieved_vertices);
				}

				if (existPPLink(node_id)) {
					pp_possible_initial_matches = getCandidatePP(node_id);
				}

				if (existNormalLink(node_id) && existPPLink(node_id)) {
					// System.out.println("Node " + node_id + " has both pp and
					// normal links");
					// System.out.println("\tBefore retain : " +
					// retrieved_vertices);
					retrieved_vertices.retainAll(pp_possible_initial_matches);
					// System.out.println("\tAfter retain : " +
					// retrieved_vertices);
				} else if (!existNormalLink(node_id)) {
					retrieved_vertices = pp_possible_initial_matches;
				}

				counter = retrieved_vertices.size();

				possible_candidates.put(node_id, retrieved_vertices);
				// System.out.println("> possible_candidates add : " + node_id +
				// " -> " + possible_candidates);
			}
			if (counter == 0) {
				max_id = node_id;
				no_sol = true;
			}
		}

		if (no_sol) {
			ordering[0] = max_id;
		} else {
			MutableIntSet chooseFirstNode = core_set;
			chooseFirstNode = chooseMaxSatNodes(chooseFirstNode);
			chooseFirstNode = chooseMaxLinks(chooseFirstNode);
			ordering[0] = chooseFirstNode.min();
		}

		// System.out.println("First element of ordering : " + ordering[0]);

		IntHashSet already_considered = new IntHashSet();
		IntHashSet not_yet_consider = new IntHashSet();
		not_yet_consider.addAll(core_set);

		not_yet_consider.remove(ordering[0]);
		already_considered.add(ordering[0]);

		int i = 1;

		// for all non ordered yet query cores
		while (not_yet_consider.size() > 0) {
			IntHashSet topRankedTie = not_yet_consider;
			topRankedTie = connectivityTopRanked(already_considered, topRankedTie);
			topRankedTie = connectivityTopRanked2Hop(already_considered, topRankedTie);
			topRankedTie = chooseMoreSelective(already_considered, topRankedTie);
			topRankedTie = chooseMoreNovelCoverage(already_considered, topRankedTie);
			int temp_node_id = topRankedTie.max();
			ordering[i] = temp_node_id;
			not_yet_consider.remove(temp_node_id);
			already_considered.add(temp_node_id);
			++i;
		}
		return ordering;
	}

	public IntArrayList selectVariableProjection() {
		IntArrayList res = new IntArrayList();
		for (String st : headerList) {
			res.add(token2id.get(st));
		}
		res.sortThis();
		return res;
	}

	public void addSelect(String token) {
		headerList.add(token);
	}

	public int size() {
		TreeSet<Integer> ris = new TreeSet<Integer>();
		MutableIntIterator it = in_list.keySet().intIterator();
		while (it.hasNext())
			ris.add(it.next());
		it = out_list.keySet().intIterator();
		while (it.hasNext())
			ris.add(it.next());
		return ris.size();
	}

	// For each Pair connected by a set of predicates, creates a vector and
	// index it by the pair.
	private void createVectorRepresentation() {
		Set<query.Pair> keys = pair2dims.keySet();
		for (query.Pair el : keys) {
			pair2dims_vec.put(el, pair2dims.get(el).toArray());
		}
	}

	// Returns all predicates linking two query nodes.
	// If they are not such predicates, returns an empty array.
	public short[] getDims(int source, int sink) {
		query.Pair p = new query.Pair(source, sink);
		if (pair2dims_vec.containsKey(p)) {
			return pair2dims_vec.get(p);
		} else {
			return new short[0];
		}

	}

	/*
	 * return the order to process the query nodes
	 * 
	 */
	public Vector<ObjectPath> getQueryStructure() {
		decompose(); // sat and cores
		createVectorRepresentation(); // hash of (s,o) -> [p1,p2,...]
		int[] queryOrder = getOrdering();
		// System.out.println("ordering : " + Arrays.toString(queryOrder));

		Vector<ObjectPath> path = new Vector<ObjectPath>();
		ObjectPath first = new ObjectPath(queryOrder[0], 0);
		// manage the selfLoop case in the query structure for node in position
		// 0
		if (selfLoop.containsKey(queryOrder[0])) {
			first.addSelfLoopNormal((selfLoop.get(queryOrder[0]).toArray()));
		}
		if (selfLoopPP.containsKey(queryOrder[0])) {
			first.addSelfLoopPP(selfLoopPP.get(queryOrder[0]));
		}

		if (notVariable.containsKey(queryOrder[0])) {
			first.isLiteralOrUri = true;
			first.literalOrUriCode = notVariable.get(queryOrder[0]);
		}
		MutableIntIterator it_sat = cores2sats.get(first.id).intIterator();

		// For each satellite of the first core node
		while (it_sat.hasNext()) {
			int id_sat = it_sat.next();
			Pair out_sat = new Pair(first.id, id_sat);
			if (pair2dims_vec.containsKey(out_sat)) {
				first.addNormalSatelliteOut(id_sat, pair2dims_vec.get(out_sat));
			}
			if (pair2ast.containsKey(out_sat)) {
				first.addPPSatelliteOut(id_sat, pair2ast.get(out_sat));
			}
			Pair in_sat = new Pair(id_sat, first.id);
			if (pair2dims_vec.containsKey(in_sat)) {
				first.addNormalSatelliteIn(id_sat, pair2dims_vec.get(in_sat));
			}
			if (pair2ast.containsKey(in_sat)) {
				first.addPPSatelliteIn(id_sat, pair2ast.get(in_sat));
			}
		}

		// System.out.println("first object path : " + first);

		path.add(first);
		for (int i = 1; i < queryOrder.length; ++i) {
			// System.out.println("Handling next query node : " +
			// queryOrder[i]);
			ObjectPath current = new ObjectPath(queryOrder[i], i);
			// manage the selfLoop case in the query structure for node in
			// position i
			if (selfLoop.containsKey(queryOrder[i])) {
				current.addSelfLoopNormal((selfLoop.get(queryOrder[i]).toArray()));
			}
			if (selfLoopPP.containsKey(queryOrder[i])) {
				current.addSelfLoopPP(selfLoopPP.get(queryOrder[i]));
			}
			if (notVariable.containsKey(queryOrder[i])) {
				current.isLiteralOrUri = true;
				current.literalOrUriCode = notVariable.get(queryOrder[i]);
			}

			// For each core node preceding in the order
			for (int j = 0; j < i; ++j) {
				int previous_id = queryOrder[j];
				// if the current node is connected to a previous core node, add
				// link to the object path
				if (out_list.get(current.id) != null && ((IntHashSet) out_list.get(current.id)).contains(previous_id)) {
					Pair p = new Pair(current.id, previous_id);
					if (pair2ast.containsKey(p)) {
						current.addPPLink(previous_id, j, Settings.IN, pair2ast.get(p));
					}
					if (pair2dims.containsKey(p)) {
						current.addNormalLink(previous_id, j, Settings.IN, pair2dims_vec.get(p));
					}
				}
				if (in_list.get(current.id) != null && ((IntHashSet) in_list.get(current.id)).contains(previous_id)) {
					Pair p = new Pair(previous_id, current.id);
					if (pair2ast.containsKey(p)) {
						current.addPPLink(previous_id, j, Settings.OUT, pair2ast.get(p));
					}
					if (pair2dims.containsKey(p)) {
						current.addNormalLink(previous_id, j, Settings.OUT, pair2dims_vec.get(p));
					}
				}
			}

			current.sort();

			it_sat = cores2sats.get(current.id).intIterator();
			while (it_sat.hasNext()) {
				int id_sat = it_sat.next();
				Pair out_sat = new Pair(current.id, id_sat);
				if (pair2dims_vec.containsKey(out_sat)) {
					// current.satellites_out.put(id_sat,
					// pair2dims_vec.get(out_sat));
					current.addNormalSatelliteOut(id_sat, pair2dims_vec.get(out_sat));
				}
				if (pair2ast.containsKey(out_sat)) {
					first.addPPSatelliteOut(id_sat, pair2ast.get(out_sat));
				}
				Pair in_sat = new Pair(id_sat, current.id);
				if (pair2dims_vec.containsKey(in_sat)) {
					// current.satellites_in.put(id_sat,
					// pair2dims_vec.get(in_sat));
					current.addNormalSatelliteIn(id_sat, pair2dims_vec.get(in_sat));
				}
				if (pair2ast.containsKey(in_sat)) {
					first.addPPSatelliteIn(id_sat, pair2ast.get(in_sat));
				}
			}
			path.add(current);
		}
		return path;
	}

	public Vector<ObjectPath> getPath() {
		return this.path;
	}

	public LinkedList<int[]> getResults() {
		return results;
	}

	public IntArrayList getProjection() {
		return projection;
	}

	// IN (positive) OUT (negative)
	// feature 1: maximum cardinality of a set in the vertex signature
	// feature 2: number of unique dimension in the vertex signature
	// feature 3: minimum index value of the edge type
	// feature 4: maximum index value of the edge type
	public SimplePointND getSynopsis(int v_id) {
		short[] syn = new short[Settings.SYNOPSIS_SIZE];
		syn[2] = syn[2 + Settings.N_FEAT] = Short.MIN_VALUE;
		MutableIntIterator itr = null;
		IntHashSet unique_dims = null;

		/* BUILD THE SYNOPSIS FOR INCOMING LIST */
		if (in_list.get(v_id) != null) {
			itr = ((IntHashSet) in_list.get(v_id)).intIterator();
			unique_dims = new IntHashSet();
			while (itr.hasNext()) {
				Pair p_temp = new Pair(itr.next(), v_id);
				if (!pair2ast.containsKey(p_temp)) {
					ShortHashSet dims = pair2dims.get(p_temp);
					syn[0] = (short) ((dims.size() > syn[0]) ? pair2dims.get(p_temp).size() : syn[0]);
					MutableShortIterator it_short = dims.shortIterator();
					while (it_short.hasNext()) {
						short s = it_short.next();
						syn[2] = (short) ((s < (-1 * syn[2])) ? (-1 * s) : syn[2]);
						syn[3] = (s > syn[3]) ? s : syn[3];
						unique_dims.add(s);
					}
				}
			}
			syn[1] = (short) unique_dims.size();
		}

		/* BUILD THE SYNOPSIS FOR OUTCOMING LIST */
		if (out_list.get(v_id) != null) {
			itr = ((IntHashSet) out_list.get(v_id)).intIterator();
			unique_dims = new IntHashSet();
			while (itr.hasNext()) {
				Pair p_temp = new Pair(v_id, itr.next());
				if (!pair2ast.containsKey(p_temp)) {
					ShortHashSet dims = pair2dims.get(p_temp);
					syn[0 + Settings.N_FEAT] = (short) ((dims.size() > syn[0 + Settings.N_FEAT])
							? pair2dims.get(p_temp).size() : syn[0 + Settings.N_FEAT]);
					MutableShortIterator it_short = dims.shortIterator();
					while (it_short.hasNext()) {
						short s = it_short.next();
						syn[2 + Settings.N_FEAT] = (short) ((s < (-1 * syn[2 + Settings.N_FEAT])) ? (-1 * s)
								: syn[2 + Settings.N_FEAT]);
						syn[3 + Settings.N_FEAT] = (s > syn[3 + Settings.N_FEAT]) ? s : syn[3 + Settings.N_FEAT];
						unique_dims.add(s);
					}
				}
			}
			syn[1 + Settings.N_FEAT] = (short) unique_dims.size();
		}
		SimplePointND s = new SimplePointND(syn);
		// System.out.println("> Returning " + s);
		return s;
	}

	public String convertIdToToken(int id) {
		return this.id2token.get(id);
	}

	public int convertToken2Id(String token) {
		return this.token2id.get(token);
	}

	/**
	 * Builds up structures given a query triple. If the current triple has a
	 * property path, considers pair2ast instead of pair2dims.
	 * 
	 * @param source
	 * @param sink
	 * @param dim
	 * @param subjectCode
	 * @param objectCode
	 * @param ast
	 */
	public void addTriple(String source, String sink, short dim, int subjectCode, int objectCode, QueryTree ast) {
		if (!token2id.containsKey(source)) {
			int val = token2id.size();
			token2id.put(source, val);
			id2token.put(val, source);
		}

		if (!token2id.containsKey(sink)) {
			int val = token2id.size();
			token2id.put(sink, val);
			id2token.put(val, sink);
		}
		int id_source = token2id.get(source);
		int id_sink = token2id.get(sink);

		if (subjectCode != Settings.VARIABLE) {
			notVariable.put(id_source, GoppeGraphDatabase.getDatabase().getString2intSO().get(source));
		}

		if (objectCode != Settings.VARIABLE) {
			notVariable.put(id_sink, GoppeGraphDatabase.getDatabase().getString2intSO().get(sink));
		}

		// Case of a loop ?x -> ?x
		// Must consider property paths too
		if (id_source == id_sink) {
			if (ast == null) {
				if (!selfLoop.containsKey(id_source))
					selfLoop.put(id_source, new ShortHashSet());
				selfLoop.get(id_source).add(dim);
			} else {
				if (!selfLoopPP.containsKey(id_source))
					selfLoopPP.put(id_source, new ArrayList<>());
				selfLoopPP.get(id_source).add(ast);
			}
		}

		if (!in_list.containsKey(id_sink))
			in_list.put(id_sink, new IntHashSet());
		in_list.get(id_sink).add(id_source);

		if (!out_list.containsKey(id_source))
			out_list.put(id_source, new IntHashSet());
		out_list.get(id_source).add(id_sink);

		Pair pair = new Pair(id_source, id_sink);
		if (ast == null) {
			if (!pair2dims.containsKey(pair))
				pair2dims.put(pair, new ShortHashSet());
			pair2dims.get(pair).add(dim);
			normalLinkNodes.add(id_source);
			normalLinkNodes.add(id_sink);
		} else {
			if (!pair2ast.containsKey(pair))
				pair2ast.put(pair, new ArrayList<QueryTree>());
			pair2ast.get(pair).add(ast);
			ppLinkNodes.add(id_source);
			ppLinkNodes.add(id_sink);
		}
	}

	public HashMap<Pair, ArrayList<QueryTree>> getPair2Ast() {
		return this.pair2ast;
	}

	static String readFile(String path, Charset encoding) throws IOException {
		byte[] encoded = Files.readAllBytes(Paths.get(path));
		return new String(encoded, encoding);
	}

	public boolean isAllPP() {
		return allPP;
	}

	public void setAllPP(boolean allPP) {
		this.allPP = allPP;
	}

	/**
	 * Returns a String formated with the query results.
	 * 
	 * @return
	 */
	public String formatResults() {

		StringBuilder sb = new StringBuilder();
		for (int[] r : getResults()) {
			for (int x = 0; x < r.length; x++) {
				sb.append(convertIdToToken(getProjection().get(x)) + " = "
						+ GoppeGraphDatabase.getDatabase().getInt2stringSO().get(r[x]) + ", ");
			}
			sb.setLength(sb.length() - 2);
			sb.append("\n");
		}
		return sb.toString();

	}
}
