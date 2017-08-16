/**
 * 
 * Class that implements the Graph Database model. This class contains all the procedure 
 * to transform an RDF dataset into its corresponding mulitgraph representation 
 * 
 * 
 * 
 * */

package data;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.apache.jena.graph.Node;
import org.apache.jena.graph.NodeFactory;
import org.apache.jena.sparql.core.TriplePath;
import org.apache.jena.sparql.path.Path;
import org.apache.jena.sparql.path.PathParser;
import org.apache.jena.sparql.sse.SSE;
import org.apache.jena.sparql.syntax.ElementPathBlock;
import org.khelekore.prtree.NDMBRConverter;
import org.khelekore.prtree.PRTree;
import org.khelekore.prtree.SimplePointND;

import com.gs.collections.api.iterator.MutableIntIterator;
import com.gs.collections.impl.list.mutable.FastList;
import com.gs.collections.impl.list.mutable.primitive.IntArrayList;
import com.gs.collections.impl.map.mutable.primitive.IntObjectHashMap;
import com.gs.collections.impl.map.mutable.primitive.ObjectIntHashMap;
import com.gs.collections.impl.map.mutable.primitive.ShortIntHashMap;
import com.gs.collections.impl.set.mutable.primitive.IntHashSet;

import propertypaths.Inverser;
import propertypaths.PairInt;
import propertypaths.QueryTree;
import query.LinkObjectPath;
import query.NormalLinkPath;
import query.ObjectPath;
import query.PPLinkPath;
import query.Query;

public class GraphDatabase {

	/*
	 * the R-Tree employed to store the synopsis representaiton of the vertex
	 */
	private PRTree prtree;
	/*
	 * An inverted list that given a synopsis return the list of the vertices
	 * corresponding a that synopsis In the worst case this list contains as
	 * many synopsis as the number of vertices in the multigraph. Practically,
	 * many vertices have the same synopsis
	 * 
	 */
	private HashMap<SimplePointND, IntArrayList> compacted_synopsis;

	/*
	 * An Hash Table that has the selectivity for each predicate in the RDF data
	 */
	private ShortIntHashMap predicates_occurrences;

	/*
	 * @param synopsis: a synopsis representation of a vertex
	 * 
	 * @return the list of vertices, in the RDF multigraph, that match the
	 * specific synopsis
	 */

	public IntHashSet getNodeList(SimplePointND synopsis) {
		List<SimplePointND> resultNodes = new FastList<SimplePointND>();
		prtree.getNotDominatedPoints(synopsis, resultNodes);
		IntHashSet possible_initial_matches = new IntHashSet();
		for (SimplePointND t : resultNodes) {
			possible_initial_matches.addAll(compacted_synopsis.get(t));
		}
		return possible_initial_matches;
	}

	/*
	 * first Integer : Subject/Object ID second Integer : Predicate ID
	 * LinkedList<Integer> : list of nodes connected by the specific predicate
	 */

	public PRTree getPrtree() {
		return prtree;
	}

	public HashMap<SimplePointND, IntArrayList> getCompacted_synopsis() {
		return compacted_synopsis;
	}

	public ShortIntHashMap getPredicates_occurrences() {
		return predicates_occurrences;
	}

	/**
	 * Builds the synopsis structure used to retrieve candidates.
	 */
	private void createSynopsisStructure() {
		short[][] synopsis;
		synopsis = new short[GoppeGraphDatabase.getDatabase().getInt2StringSO().size()][Settings.N_FEAT * 2];

		for (int i = 0; i < synopsis.length; ++i)
			synopsis[i][2] = synopsis[i][2 + Settings.N_FEAT] = Short.MIN_VALUE;

		int[] nodes = GoppeGraphDatabase.getDatabase().getInt2stringSO().keySet().toArray();
		for (int n : nodes) {
			if (GoppeGraphDatabase.getDatabase().getPredsOut(n) != null) {
				int[] preds = GoppeGraphDatabase.getDatabase().getPredsOut(n).keySet().toArray();

				// feature 1 - maximum cardinality
				ObjectIntHashMap<PairInt> pairCounter = GoppeGraphDatabase.getDatabase().getPairCounter();
				ObjectIntHashMap<PairInt> tempPair = new ObjectIntHashMap<>();
				Iterator<PairInt> it = pairCounter.keySet().iterator();
				while (it.hasNext()) {
					PairInt i = it.next();
					if (i.getLeft() == n) {
						tempPair.put(i, pairCounter.get(i));
					}
				}
				int maxCardinality = tempPair.max();
				if (synopsis[n][0 + Settings.N_FEAT] < maxCardinality)
					synopsis[n][0 + Settings.N_FEAT] = (short) maxCardinality;

				// feature 2: number of unique dimension in the vertex signature
				synopsis[n][1 + Settings.N_FEAT] = (short) preds.length;

				for (int p : preds) {
					// System.out.println("\t" + p);
					// feature 3: minimum index value of the edge type
					if (synopsis[n][2 + Settings.N_FEAT] < (p * -1))
						synopsis[n][2 + Settings.N_FEAT] = (short) (p * -1);

					// feature 4: maximum index value of the edge type

					if (synopsis[n][3 + Settings.N_FEAT] < p)
						synopsis[n][3 + Settings.N_FEAT] = (short) p;
				}
			}

			if (GoppeGraphDatabase.getDatabase().getPredsIn(n) != null) {
				int[] preds = GoppeGraphDatabase.getDatabase().getPredsIn(n).keySet().toArray();

				// feature 1 - maximum cardinality
				ObjectIntHashMap<PairInt> pairCounter = GoppeGraphDatabase.getDatabase().getPairCounter();
				ObjectIntHashMap<PairInt> tempPair = new ObjectIntHashMap<>();
				Iterator<PairInt> it = pairCounter.keySet().iterator();
				while (it.hasNext()) {
					PairInt i = it.next();
					if (i.getRight() == n) {
						tempPair.put(i, pairCounter.get(i));
					}
				}
				int maxCardinality = tempPair.max();
				if (synopsis[n][0] < maxCardinality)
					synopsis[n][0] = (short) maxCardinality;

				// feature 2: number of unique dimension in the vertex signature
				synopsis[n][1] = (short) preds.length;

				for (int p : preds) {
					// feature 3: minimum index value of the edge type
					if (synopsis[n][2] < (p * -1))
						synopsis[n][2] = (short) (p * -1);

					// feature 4: maximum index value of the edge type

					if (synopsis[n][3] < p)
						synopsis[n][3] = (short) p;
				}
			}
		}

		for (int i = 0; i < synopsis.length; ++i) {
			SimplePointND temp = new SimplePointND(synopsis[i]);
			// System.out.println("temp synopsis : " + temp);
			if (!compacted_synopsis.containsKey(temp))
				compacted_synopsis.put(temp, new IntArrayList());
			compacted_synopsis.get(temp).add(i);
		}
	}

	/**
	 * Main method called to compute SPARQL solutions of the given
	 * {@link Query}.
	 * 
	 * @param query
	 */
	public void query(Query query) {

		IntObjectHashMap<ArrayList<Integer>> sats_list = new IntObjectHashMap<ArrayList<Integer>>();
		IntObjectHashMap<HashMap<Integer, ArrayList<Integer>>> buffer_neigh = new IntObjectHashMap<>();
		List<SimplePointND> resultNodes = new FastList<SimplePointND>();
		IntHashSet possible_initial_matches = new IntHashSet();
		IntHashSet pp_possible_initial_matches = new IntHashSet();

		ObjectPath constraint = query.getPath().get(0);

		// if the first query node in the ranking is a literal or an URI, load
		// directly its identifier
		if (constraint.isLiteralOrUri) {
			possible_initial_matches.add(constraint.literalOrUriCode);
		} else {// otherwise if it is a variable ?x, query the R-TREE structure
				// and retrieve the possible matches
			// We need to do the intersection of the candidates of each link
			if (query.existNormalLink(constraint.id)) {
				SimplePointND query_r_tree = query.getSynopsis(constraint.id);
				prtree.getNotDominatedPoints(query_r_tree, resultNodes);
				// System.out.println("results of syn " + resultNodes);
				for (SimplePointND t : resultNodes) {
					possible_initial_matches.addAll(compacted_synopsis.get(t));
				}
			}

			if (query.existPPLink(constraint.id)) {
					pp_possible_initial_matches = query.getCandidatePP(constraint.id);
			}

			if (query.existNormalLink(constraint.id) && query.existPPLink(constraint.id)) {
				possible_initial_matches.retainAll(pp_possible_initial_matches);
			} else if (!query.existNormalLink(constraint.id)) {
				possible_initial_matches = pp_possible_initial_matches;
			}
		}

		int[] current_sol = new int[query.size()];
		MutableIntIterator itr = possible_initial_matches.intIterator();

		// for each possible node in the graph matching the root of the spanning
		// tree
		while (itr.hasNext()) {
			int current_val = itr.next();
			boolean selfLoop = true;
			if (constraint.selfLoop != null) {
				for (LinkObjectPath l : constraint.selfLoop) {
					if (l.linkType == 0) {
						selfLoop = selfLoop && GoppeGraphDatabase.getDatabase().checkIfNeighExists(current_val,
								current_val, ((NormalLinkPath) l).dims, Settings.IN);
					} else {
						// property path link
						PPLinkPath s = (PPLinkPath) l;
						s.direction = Settings.IN;
						selfLoop = selfLoop && existsPathBetween(current_val, current_val, s, query);
					}
				}

			}
			if (selfLoop && checkSatNodes(current_val, constraint, sats_list, query.notVariable, query)) {
				current_sol[constraint.id] = current_val;
				backtrackingCheck(current_sol, 1, query, buffer_neigh, sats_list, "\t");
				buffer_neigh.remove(constraint.id);
			}
		}
	}

	private void backtrackingCheck(int[] current_sol, int level, Query query,
			IntObjectHashMap<HashMap<Integer, ArrayList<Integer>>> buffer_neigh,
			IntObjectHashMap<ArrayList<Integer>> sat_list, String offset) {
		// terminate the recursion if the procedure gets a solution for the
		// whole set of nodes that meet the constraints
		if (level == (query.getPath().size())) {
			// System.out.println(">>>> Combining cores and satellites, level :
			// " + level);
			combineCoreAndSatellites(current_sol, sat_list, query);
			Iterator<int[]> rit = query.getResults().iterator();
			// System.out.println(">>>> After combination");
			while (rit.hasNext()) {
				int[] r = rit.next();
				// System.out.print(">>>>");
				for (int i = 0; i < r.length; i++) {
					// System.out.print(" " + r[i]);
				}
				// System.out.println();
			}
		} else {
			ObjectPath constraints = query.getPath().get(level);
			LinkObjectPath link = constraints.previous_links_cores.get(0);
			ArrayList<Integer> current_match_set = null;
			if (constraints.isLiteralOrUri) {
				current_match_set = new ArrayList<>();
				current_match_set.add(constraints.literalOrUriCode);
				// Here check if it is a classic link or a property path link
				Integer t = current_sol[query.getPath().get(link.rank_previous_id).id];
				ArrayList<Integer> first_constraints = GoppeGraphDatabase.getDatabase().query(t,
						((NormalLinkPath) link).dims, link.direction);
				// System.out.println(">> first constraints : " +
				// first_constraints);
				current_match_set.retainAll(first_constraints);

			} else {
				// System.out.println(">>> Processing query node " +
				// query.convertIdToToken(constraints.id) + " ("
				// + constraints.id + ")");
				// Here check if it is a classic link or a property path link
				if (link.linkType == 0) {
					// current match set is the set of vertices in the graph
					// matching the link
					// System.out.println(">>> with normal link : " + link);
					Integer t = current_sol[query.getPath().get(link.rank_previous_id).id];
					current_match_set = GoppeGraphDatabase.getDatabase().query(t, ((NormalLinkPath) link).dims,
							link.direction);
					// System.out.println(">>> current match set : " +
					// current_match_set);
				} else {
					current_match_set = computeSolutionsPPLinkPath(link, constraints.id, query, false);
					// System.out.println(">> current match set : " +
					// current_match_set);
				}
			}
			// System.out.println(">>> possible candidates ? " +
			// query.possible_candidates);
			// System.out.println(
			// ">>> Retaining " + query.possible_candidates.get(constraints.id)
			// + " from current match set");
			IntHashSet qpc = query.possible_candidates.get(constraints.id);
			MutableIntIterator iit = qpc.intIterator();
			while (iit.hasNext()) {
				current_match_set.remove(current_match_set.indexOf(iit.next()));
			}

			// System.out.println(">>> current match set post retain : " +
			// current_match_set);

			// Green edges, the structural edges
			for (int i = constraints.previous_links_cores.size(); --i >= 1 && current_match_set.size() > 0;) {
				int prev_node_id = query.getPath().get(constraints.previous_links_cores.get(i).rank_previous_id).id;
				int prev_vertex_id = current_sol[prev_node_id];
				ArrayList<Integer> constraint_match_set = null;

				if (buffer_neigh.containsKey(prev_node_id)) {
					if (((HashMap<Integer, ArrayList<Integer>>) buffer_neigh.get(prev_node_id))
							.containsKey(constraints.id)) {
						constraint_match_set = ((HashMap<Integer, ArrayList<Integer>>) buffer_neigh.get(prev_node_id))
								.get(constraints.id);
					} else {
						if (link.linkType == 0) {
							// Normal link
							constraint_match_set = GoppeGraphDatabase.getDatabase().query(prev_vertex_id,
									((NormalLinkPath) constraints.previous_links_cores.get(i)).dims,
									constraints.previous_links_cores.get(i).direction);
						} else {
							// Property path link
							constraint_match_set = computeSolutionsPPLinkPath(link, constraints.id, query, false);
							// System.out.println(">>> constraint match set : "
							// + constraint_match_set);
						}
						// Adding buffered neighbors (avoids redondant
						// computation)
						((HashMap<Integer, ArrayList<Integer>>) buffer_neigh.get(prev_node_id)).put(constraints.id,
								constraint_match_set);
					}
				} else {
					if (link.linkType == 0) {
						// Normal link
						constraint_match_set = GoppeGraphDatabase.getDatabase().query(prev_vertex_id,
								((NormalLinkPath) constraints.previous_links_cores.get(i)).dims,
								constraints.previous_links_cores.get(i).direction);
					} else {
						// Property path link
						constraint_match_set = computeSolutionsPPLinkPath(link, constraints.id, query, false);
					}
					buffer_neigh.put(prev_node_id, new HashMap<Integer, ArrayList<Integer>>());
					((HashMap<Integer, ArrayList<Integer>>) buffer_neigh.get(prev_node_id)).put(constraints.id,
							constraint_match_set);

				}
				current_match_set.retainAll(constraint_match_set);
			}

			for (Integer current_val : current_match_set) {
				boolean selfLoop = true;
				if (constraints.selfLoop != null)
					for (LinkObjectPath l : constraints.selfLoop) {
						if (l.linkType == 0) {
							selfLoop = selfLoop && GoppeGraphDatabase.getDatabase().checkIfNeighExists(current_val,
									current_val, ((NormalLinkPath) l).dims, Settings.IN);
						} else {
							// property path link
							PPLinkPath s = (PPLinkPath) l;
							s.direction = Settings.IN;
							selfLoop = selfLoop && existsPathBetween(current_val, current_val, s, query);
						}
					}

				if (selfLoop && checkSatNodes(current_val, constraints, sat_list, query.notVariable, query)) {
					current_sol[constraints.id] = current_val;
					backtrackingCheck(current_sol, level + 1, query, buffer_neigh, sat_list, offset + "\t");
					buffer_neigh.remove(constraints.id);
				}
			}
		}

	}

	/* The heuristics to order the nodes of the query from the 2 to the last */
	private boolean checkSatNodes(int vertex_id, ObjectPath constraint, IntObjectHashMap<ArrayList<Integer>> sats_list,
			IntObjectHashMap<Integer> notVariable, Query query) {
		// System.out.println("Entering checkSatNodes");

		boolean meet_constraints = true;
		IntObjectHashMap<ArrayList<Integer>> loc_sat_list = new IntObjectHashMap<ArrayList<Integer>>();
		MutableIntIterator in_it = constraint.satellites_in.keySet().intIterator();
		while (in_it.hasNext() && meet_constraints) {
			ArrayList<Integer> temp = null;
			int sat_id = in_it.next();
			// System.out.println("CHECKING SAT INC : " + vertex_id + ", sat : "
			// + sat_id);
			if (notVariable.containsKey(sat_id)) {
				LinkObjectPath sats = constraint.satellites_in.get(sat_id);
				if (sats.linkType == 0) {
					NormalLinkPath dims = (NormalLinkPath) constraint.satellites_in.get(sat_id);
					meet_constraints = meet_constraints && GoppeGraphDatabase.getDatabase()
							.checkIfNeighExists(vertex_id, notVariable.get(sat_id), dims.dims, Settings.IN);
				} else {
					// property path link
					PPLinkPath s = (PPLinkPath) sats;
					s.direction = Settings.OUT;
					meet_constraints = meet_constraints
							&& existsPathBetween(notVariable.get(sat_id), vertex_id, s, query);
				}
				if (meet_constraints) {
					temp = new ArrayList<Integer>(Settings.ARRAY_SIZE);
					temp.add(notVariable.get(sat_id));
				}
			} else {
				LinkObjectPath sats = constraint.satellites_in.get(sat_id);
				if (sats.linkType == 0) {
					NormalLinkPath dims = (NormalLinkPath) sats;
					temp = GoppeGraphDatabase.getDatabase().query(vertex_id, dims.dims, Settings.IN);
				} else {
					// property path link
					PPLinkPath s = (PPLinkPath) sats;
					s.direction = Settings.OUT;
					temp = computeSolutionsPPLinkPath(s, vertex_id, query, true);
					// System.out.println("FOUND SOLUTIONS CHECK SAT NODES FOR
					// PP IN : " + temp);
				}

				if (temp.size() == 0)
					meet_constraints = false;
			}
			loc_sat_list.put(sat_id, temp);
		}

		MutableIntIterator out_it = constraint.satellites_out.keySet().intIterator();
		while (out_it.hasNext() && meet_constraints) {
			int sat_id = out_it.next();
			// System.out.println("CHECKING SAT OUT : " + vertex_id + ", sat : "
			// + sat_id);
			ArrayList<Integer> temp = null;
			if (notVariable.containsKey(sat_id)) {
				LinkObjectPath sats = constraint.satellites_out.get(sat_id);
				if (sats.linkType == 0) {
					NormalLinkPath dims = (NormalLinkPath) constraint.satellites_out.get(sat_id);
					meet_constraints = meet_constraints && GoppeGraphDatabase.getDatabase()
							.checkIfNeighExists(vertex_id, notVariable.get(sat_id), dims.dims, Settings.OUT);
				} else {
					// property path link
					PPLinkPath s = (PPLinkPath) sats;
					s.direction = Settings.IN;
					meet_constraints = meet_constraints
							&& existsPathBetween(notVariable.get(sat_id), vertex_id, s, query);
				}
				if (meet_constraints) {
					temp = new ArrayList<Integer>();
					temp.add(notVariable.get(sat_id));
				}
			} else {
				LinkObjectPath sats = constraint.satellites_out.get(sat_id);
				if (sats.linkType == 0) {
					NormalLinkPath dims = (NormalLinkPath) sats;
					temp = GoppeGraphDatabase.getDatabase().query(vertex_id, dims.dims, Settings.OUT);
				} else {
					// Property path link
					PPLinkPath pp = (PPLinkPath) sats;
					pp.direction = Settings.IN;
					temp = computeSolutionsPPLinkPath(pp, vertex_id, query, true);
					// System.out.println("FOUND SOLUTIONS CHECK SAT NODES FOR
					// PP OUT :" + temp);
				}
				if (temp.size() == 0)
					meet_constraints = false;
			}

			if (loc_sat_list.containsKey(sat_id) && meet_constraints) {
				loc_sat_list.get(sat_id).retainAll(temp);
				if (loc_sat_list.get(sat_id).size() == 0)
					meet_constraints = false;
			} else {
				loc_sat_list.put(sat_id, temp);
			}
		}

		if (meet_constraints) {
			MutableIntIterator it = loc_sat_list.keySet().intIterator();
			while (it.hasNext()) {
				int val = it.next();
				sats_list.put(val, loc_sat_list.get(val));
			}
		}
		return meet_constraints;
	}

	// For each core node, generates all solutions by combining satellites if it
	// fits the solution.
	private void combineCoreAndSatellites(int[] current_sol, IntObjectHashMap<ArrayList<Integer>> sat_list,
			Query query) {
		// System.out.println("current_sol : " + Arrays.toString(current_sol));
		// System.out.println("Sat list : " + sat_list);
		// int[] temp_sol = Arrays.copyOf(current_sol, current_sol.length);
		int[] sat_position = sat_list.keySet().toArray();
		int sat_idx = 0;
		for (Integer c : sat_list.get(sat_position[sat_idx])) {
			current_sol[sat_position[sat_idx]] = c;
			// System.out.println("> current_sol : " +
			// Arrays.toString(current_sol));
			generateSol(current_sol, sat_idx + 1, sat_position, query.getResults(), sat_list, query.getProjection());
		}
	}

	private void generateSol(int[] current_sol, int sat_idx, int[] sat_position, LinkedList<int[]> results,
			IntObjectHashMap<ArrayList<Integer>> sat_list, IntArrayList projection) {
		if (sat_idx == sat_position.length) {
			int[] proj_res = new int[projection.size()];
			MutableIntIterator itr = projection.intIterator();
			int i = 0;
			while (itr.hasNext()) {
				proj_res[i++] = current_sol[itr.next()];
			}
			results.add(proj_res);
		} else {
			for (int c : sat_list.get(sat_position[sat_idx])) {
				current_sol[sat_position[sat_idx]] = c;
				generateSol(current_sol, sat_idx + 1, sat_position, results, sat_list, projection);
			}
		}
	}

	private ArrayList<Integer> computeSolutionsPPLinkPath(LinkObjectPath link, Integer start, Query query,
			boolean sat) {
		ArrayList<Integer> toReturn = new ArrayList<>();

		// PP Stuff with GoPPe
		PPLinkPath pp = (PPLinkPath) link;
		// System.out.println("Direction of link : " + link.direction);
		QueryTree p = pp.pps.get(0); //
		QueryTree toProcess = p;
		String n = (String) GoppeGraphDatabase.getDatabase().getInt2StringSO().get(start);
		int mapping = GoppeGraphDatabase.getDatabase().convertStringToIntSO(n);
		if (link.direction == Settings.OUT && !p.getInitialPP().startsWith("!")) {
			// Need to inverse pp
			String toInverse = new Inverser("^(" + p.getInitialPP() + ")").getInversed();
			ElementPathBlock triplePattern = new ElementPathBlock();
			Node typ = NodeFactory.createVariable("typ");
			Node sometype = NodeFactory.createURI(n);
			Path path = PathParser.parse(toInverse, SSE.getPrefixMapRead());
			TriplePath tp = new TriplePath(sometype, path, typ);
			// System.out.println("PATH : " + path);
			triplePattern.addTriplePath(tp);
			toProcess = query.parsePropertyPath(tp);
			// System.out.println("Incoming PP, new reversed : " + toInverse);
		}
		toProcess.setFixedLeft();
		toProcess.setFixedStart(mapping);
		toProcess.fuseGroups();
		// computeSelectivity generates the automata (old code) and needs to be
		// called
		toProcess.computeSelectivity(toProcess.getRoot());
		if (link.direction == Settings.OUT) {
			// System.out.println("Starting property path inversed with fixed
			// start : " + mapping + " : " + toProcess);
			GoppeGraphDatabase.getDatabase().evaluateQueryTree(toProcess.getRoot());
		} else {
			// System.out.println("Starting property path with fixed start : " +
			// mapping + " : " + toProcess);
			GoppeGraphDatabase.getDatabase().evaluateQueryTree(toProcess.getRoot());
		}

		if (sat) {
			ArrayList<PairInt> solutions = toProcess.getRoot().getCurrentSolutions();
			// System.out.println("SOLUTIONS : " + solutions);
			for (PairInt s : solutions) {
				toReturn.add(s.getRight());
			}
		} else {
			ArrayList<PairInt> solutions = toProcess.getRoot().getCurrentSolutions();
			// System.out.println("SOLUTIONS : " + solutions);
			for (PairInt s : solutions) {
				toReturn.add(s.getLeft());
			}
		}
		return toReturn;
	}

	private boolean existsPathBetween(int sat_id, int vertex_id, PPLinkPath s, Query query) {
		ArrayList<Integer> sols = computeSolutionsPPLinkPath(s, sat_id, query, true);
		return sols.contains(vertex_id);
	}

	/*
	 * @param fileName The name of the .nt file that contains the RDF dataset
	 */
	public GraphDatabase(String fileName) throws IOException {

		compacted_synopsis = new HashMap<SimplePointND, IntArrayList>();
		predicates_occurrences = new ShortIntHashMap(Settings.INIT_SIZE);

		// Post-fusion with AMbER : the database used is now the one Goppe uses.
		// More compliant with UTF chars and is property paths ready.
		GoppeGraphDatabase.getDatabase(fileName);

		// To compute candidates for Amber, build the synospsis.
		createSynopsisStructure();
		prtree = new PRTree(new NDMBRConverter(Settings.SYNOPSIS_SIZE), 10);
		prtree.load(compacted_synopsis.keySet());

	}

}
