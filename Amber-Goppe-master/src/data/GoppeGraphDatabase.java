package data;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Set;
import java.util.TreeSet;

import com.gs.collections.api.iterator.MutableIntIterator;
import com.gs.collections.impl.map.mutable.primitive.IntBooleanHashMap;
import com.gs.collections.impl.map.mutable.primitive.IntObjectHashMap;
import com.gs.collections.impl.map.mutable.primitive.ObjectBooleanHashMap;
import com.gs.collections.impl.map.mutable.primitive.ObjectIntHashMap;

import propertypaths.GraphAutomaton;
import propertypaths.OPERATOR;
import propertypaths.PairInt;
import propertypaths.StateNode;
import propertypaths.TreeLeaf;
import propertypaths.TreeNode;

@SuppressWarnings({ "rawtypes", "unchecked" })
public class GoppeGraphDatabase {

	private int triplesCount = 0;
	private ObjectIntHashMap<String> string2intSO = new ObjectIntHashMap<>();
	private IntObjectHashMap int2stringSO = new IntObjectHashMap<>();
	private ObjectIntHashMap<String> string2IntP = new ObjectIntHashMap<>();
	private IntObjectHashMap int2stringP = new IntObjectHashMap<>();

	private IntObjectHashMap<TreeSet<Integer>> predicates_index_out = new IntObjectHashMap<>();
	private IntObjectHashMap<TreeSet<Integer>> predicates_index_in = new IntObjectHashMap<>();

	private IntObjectHashMap<IntObjectHashMap<ArrayList<Integer>>> fastOutNeighbors = new IntObjectHashMap<>();
	private IntObjectHashMap<IntObjectHashMap<ArrayList<Integer>>> fastInNeighbors = new IntObjectHashMap<>();

	private ObjectIntHashMap<PairInt> pairCounter = new ObjectIntHashMap<>();

	private static GoppeGraphDatabase thisDatabase = null;
	private int characterShift = 16384;

	private IntObjectHashMap<IntBooleanHashMap> negationSets = new IntObjectHashMap<>();

	private IntObjectHashMap<IntBooleanHashMap> negationSetsRev = new IntObjectHashMap<>();

	private GoppeGraphDatabase(String databasePath) {
		BufferedReader r = null;
		try {
			r = new BufferedReader(new FileReader(databasePath));

			int subjetObjectNumber = 0;
			int predicateNumber = 97; // 'a' utf-16
			String line = r.readLine();
			while (line != null) {
				line = line.substring(0, line.lastIndexOf("."));
				this.triplesCount++;

				if (this.triplesCount % 1000000 == 0)
					System.out.println(this.triplesCount);

				String[] tokens = line.split(" ");
				String subject = tokens[0];
				String predicate = tokens[1];
				String object = tokens[2];
				for (int i = 3; i < tokens.length; i++) {
					object += " " + tokens[i];
				}

				if (!string2intSO.containsKey(subject)) {
					string2intSO.put(subject, subjetObjectNumber);
					int2stringSO.put(subjetObjectNumber, subject);
					subjetObjectNumber++;
				}

				if (!string2intSO.containsKey(object)) {
					string2intSO.put(object, subjetObjectNumber);
					int2stringSO.put(subjetObjectNumber, object);
					subjetObjectNumber++;
				}

				if (!string2IntP.containsKey(predicate)) {
					string2IntP.put(predicate, predicateNumber);
					int2stringP.put(predicateNumber, predicate);

					string2IntP.put("^" + predicate, (int) (predicateNumber + characterShift));
					int2stringP.put((int) (predicateNumber + characterShift), "^" + predicate);
					predicateNumber++;
				}

				int predicateCode = string2IntP.get(predicate);
				int subjectCode = string2intSO.get(subject);
				int objectCode = string2intSO.get(object);

				PairInt pair = new PairInt(subjectCode, objectCode);
				if (!pairCounter.containsKey(pair)) {
					pairCounter.put(pair, 1);
				} else {
					pairCounter.addToValue(pair, 1);
				}

				// System.out.println(subjectCode + ", " + predicateCode + ", "
				// + objectCode);

				if (!predicates_index_out.containsKey(predicateCode)) {
					predicates_index_out.put(predicateCode, new TreeSet<Integer>());
				}
				if (!predicates_index_in.containsKey(predicateCode)) {
					predicates_index_in.put(predicateCode, new TreeSet<Integer>());
				}

				predicates_index_out.get(predicateCode).add(subjectCode);
				predicates_index_in.get(predicateCode).add(objectCode);

				if (!fastOutNeighbors.containsKey(subjectCode)) {
					fastOutNeighbors.put(subjectCode, new IntObjectHashMap<ArrayList<Integer>>());
				}

				if (!fastInNeighbors.containsKey(objectCode)) {
					fastInNeighbors.put(objectCode, new IntObjectHashMap<ArrayList<Integer>>());
				}

				if (!fastOutNeighbors.get(subjectCode).containsKey(predicateCode)) {
					fastOutNeighbors.get(subjectCode).put(predicateCode, new ArrayList<Integer>());
				}

				if (!fastInNeighbors.get(objectCode).containsKey(predicateCode)) {
					fastInNeighbors.get(objectCode).put(predicateCode, new ArrayList<Integer>());
				}

				fastOutNeighbors.get(subjectCode).get(predicateCode).add(objectCode);
				fastInNeighbors.get(objectCode).get(predicateCode).add(subjectCode);
				line = r.readLine();
			}

			r.close();
		} catch (FileNotFoundException e) {
			System.err.println("File not found.");
		} catch (IOException e) {
			System.err.println("Could not close file.");
		}
	}

	public static GoppeGraphDatabase getDatabase(String databasePath) {
		if (thisDatabase == null)
			thisDatabase = new GoppeGraphDatabase(databasePath);
		return thisDatabase;
	}

	public static GoppeGraphDatabase getDatabase() {
		return thisDatabase;
	}

	public void addNegationSet(String neg, int code) {
		// !(a|b...|c)
		negationSets.put(code, new IntBooleanHashMap());
		negationSetsRev.put(code, new IntBooleanHashMap());
		for (int i = 0; i < neg.length(); i++) {
			char c = neg.charAt(i);
			if (c != '|' && c != '(' && c != ')' && c != '!') {
				int ocode = (int) c;
				if (c < getCharacterShift())
					negationSets.get(code).put(ocode, true);
				else
					negationSetsRev.get(code).put(ocode, true);
			}
		}
	}

	public IntBooleanHashMap getNegationSet(int c) {
		return this.negationSets.get(c);
	}

	public IntBooleanHashMap getNegationSetRev(int c) {
		return this.negationSetsRev.get(c);
	}

	public int getCharacterShift() {
		return characterShift;
	}

	public int predicatesNumber() {
		return this.int2stringP.size();
	}

	public int nodesNumber() {
		return int2stringSO.size();
	}

	public IntObjectHashMap<TreeSet<Integer>> getPredicatesIndexOut() {
		return this.predicates_index_out;
	}

	public IntObjectHashMap<TreeSet<Integer>> getPredicatesIndexIn() {
		return this.predicates_index_in;
	}

	public int getTriplesCount() {
		return this.triplesCount;
	}

	public int convertStringToIntSO(String s) {
		return string2intSO.get(s);
	}

	public ObjectIntHashMap<PairInt> getPairCounter() {
		return this.pairCounter;
	}

	public int convertStringToIntP(String s) {
		return string2IntP.get(s);
	}

	/**
	 * Given a {@link GraphAutomaton} and a node (integer), starts a
	 * breadth-first search with respect to the the automaton.
	 * 
	 * This method is used for any kleenex-like expression, allowing path of
	 * arbitrary length. The semantics behind the evaluation is the following :
	 * 
	 * 
	 * @param ga
	 * @param start
	 * @return
	 */
	public ArrayList<Integer> evaluateKleenex(GraphAutomaton ga, int start, int startState, boolean backward) {
		// System.out.println("Evaluation start.");
		ArrayList<Integer> solutions = new ArrayList<>();
		ObjectBooleanHashMap<PairInt> dv = new ObjectBooleanHashMap<>();
		// HashMap<propertypaths.PairInt, Boolean> dv = new HashMap<>();

		// Breadth-first search
		LinkedList<propertypaths.PairInt> toProcess = new LinkedList<>();
		// Visited nodes

		IntBooleanHashMap dvnode = new IntBooleanHashMap();
		// HashMap<Otil, Boolean> dvnode = new HashMap<>();

		// Pair is used for simultaneous navigation between the graph and the
		// automaton
		propertypaths.PairInt startCouple = new propertypaths.PairInt(start, startState);

		// Adding the couple (start state of the automaton, start node of the
		// automaton) to the list, to bootstrap the search
		dv.put(startCouple, true);
		toProcess.push(startCouple);
		while (!toProcess.isEmpty()) {
			propertypaths.PairInt current = toProcess.poll();
			StateNode etatCourant = ga.getStates().get(current.getRight());

			Set<Integer> labels = !backward ? etatCourant.getOutLabels() : etatCourant.getInLabels();

			IntObjectHashMap<ArrayList<Integer>> neighbors = !backward ? fastOutNeighbors.get(current.getLeft())
					: fastInNeighbors.get(current.getLeft());
			IntObjectHashMap<ArrayList<Integer>> invneighbors = backward ? fastOutNeighbors.get(current.getLeft())
					: fastInNeighbors.get(current.getLeft());
			// HashMap<Integer, StateNode> currentStateNeighbors = !backward ?
			// etatCourant.getOutNeighbors()
			// : etatCourant.getInNeighbors();

			if (!backward) {
				for (Integer label : labels) {
					StateNode etatSuivant = etatCourant.getOutNeighbors().get(label); //
					// label est un label normal
					if (label < getCharacterShift()) {
						if (neighbors != null && neighbors.get(label) != null) {
							for (Integer n : neighbors.get(label)) {
								propertypaths.PairInt next = new propertypaths.PairInt(n, etatSuivant.getHashCode());
								if (!dv.get(next)) {
									toProcess.addFirst(next);
									dv.put(next, true);
								}
							}
						}
					}
					// label est un inverse
					else if (label < 2 * getCharacterShift()) {
						int newlabel = label - getCharacterShift();
						if (invneighbors != null && invneighbors.get(newlabel) != null) {
							for (Integer n : invneighbors.get(newlabel)) {
								propertypaths.PairInt next = new propertypaths.PairInt(n, etatSuivant.getHashCode());
								if (!dv.get(next)) {
									toProcess.addFirst(next);
									dv.put(next, true);
								}
							}
						}
					}
					// negation (set)
					else {
						IntBooleanHashMap forbiddenOut = negationSets.get(label);
						IntBooleanHashMap forbiddenIn = negationSetsRev.get(label);
						if (!forbiddenOut.keySet().isEmpty() && neighbors != null) {
							MutableIntIterator a = neighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenOut.get(b)) {
									for (Integer n : neighbors.get(b)) {
										propertypaths.PairInt next = new propertypaths.PairInt(n,
												etatSuivant.getHashCode());
										if (!dv.get(next)) {
											toProcess.addFirst(next);
											dv.put(next, true);
										}
									}
								}

							}
						}
						if (!forbiddenIn.keySet().isEmpty() && invneighbors != null) {
							MutableIntIterator a = invneighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenIn.get(b)) {
									for (Integer n : invneighbors.get(b)) {
										propertypaths.PairInt next = new propertypaths.PairInt(n,
												etatSuivant.getHashCode());
										if (!dv.get(next)) {
											toProcess.addFirst(next);
											dv.put(next, true);
										}
									}
								}

							}
						}
					}
				}
			} else {
				for (Integer label : labels) {
					ArrayList<StateNode> etatsSuivants = etatCourant.getInNeighbors().get(label); //

					if (label < getCharacterShift()) {
						if (neighbors != null && neighbors.get(label) != null) {
							for (Integer n : neighbors.get(label)) {
								for (StateNode x : etatsSuivants) {
									propertypaths.PairInt next = new propertypaths.PairInt(n, x.getHashCode());
									if (!dv.get(next)) {
										toProcess.addFirst(next);
										dv.put(next, true);
									}
								}
							}
						}
					} else if (label < 2 * getCharacterShift()) {
						int newlabel = label - getCharacterShift();
						if (invneighbors != null && invneighbors.get(newlabel) != null) {
							for (Integer n : invneighbors.get(newlabel)) {
								for (StateNode x : etatsSuivants) {
									propertypaths.PairInt next = new propertypaths.PairInt(n, x.getHashCode());
									if (!dv.get(next)) {
										toProcess.addFirst(next);
										dv.put(next, true);
									}
								}
							}
						}
					} else {
						IntBooleanHashMap forbiddenOut = negationSets.get(label);
						IntBooleanHashMap forbiddenIn = negationSetsRev.get(label);
						if (!forbiddenOut.keySet().isEmpty() && neighbors != null) {
							MutableIntIterator a = neighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenOut.get(b)) {
									for (Integer n : neighbors.get(b)) {
										for (StateNode etatSuivant : etatsSuivants) {
											propertypaths.PairInt next = new propertypaths.PairInt(n,
													etatSuivant.getHashCode());
											if (!dv.get(next)) {
												toProcess.addFirst(next);
												dv.put(next, true);
											}
										}
									}
								}

							}
						}
						if (!forbiddenIn.keySet().isEmpty() && invneighbors != null) {
							MutableIntIterator a = invneighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenIn.get(b + getCharacterShift())) {
									for (Integer n : invneighbors.get(b)) {
										for (StateNode etatSuivant : etatsSuivants) {
											propertypaths.PairInt next = new propertypaths.PairInt(n,
													etatSuivant.getHashCode());
											if (!dv.get(next)) {
												toProcess.addFirst(next);
												dv.put(next, true);
											}
										}
									}
								}
							}
						}
					}
				}
			}

			if (!backward && etatCourant.isFinal() && !dvnode.get(current.getLeft())) {
				solutions.add(current.getLeft());
				dvnode.put(current.getLeft(), true);
				// System.out.println("New solution : " + solution);
			} else if (backward && etatCourant.isInit() && !dvnode.get(current.getLeft())) {
				solutions.add(current.getLeft());
				dvnode.put(current.getLeft(), true);
			}
		}
		return solutions;
	}

	public ArrayList<Integer> evaluate(GraphAutomaton ga, int start, int startState, boolean backward) {
		// System.out.println("Evaluation start : (" + start + ", " + startState
		// + ")");
		ArrayList<Integer> solutions = new ArrayList<>();

		LinkedList<propertypaths.PairInt> toProcess = new LinkedList<>();
		propertypaths.PairInt startCouple = new propertypaths.PairInt(start, startState); //
		// System.out.println(startCouple);
		toProcess.push(startCouple);
		while (!toProcess.isEmpty()) {
			propertypaths.PairInt current = toProcess.pollLast();
			// System.out.println(">> processin " + current);
			StateNode etatCourant = ga.getStates().get(current.getRight());

			Set<Integer> labels = !backward ? etatCourant.getOutLabels() : etatCourant.getInLabels();

			IntObjectHashMap<ArrayList<Integer>> neighbors = !backward ? fastOutNeighbors.get(current.getLeft())
					: fastInNeighbors.get(current.getLeft());
			IntObjectHashMap<ArrayList<Integer>> invneighbors = backward ? fastOutNeighbors.get(current.getLeft())
					: fastInNeighbors.get(current.getLeft());

			if (!backward) {
				for (Integer label : labels) {
					StateNode etatSuivant = etatCourant.getOutNeighbors().get(label); //
					// label est un label normal
					if (label < getCharacterShift()) {
						if (neighbors != null && neighbors.get(label) != null) {
							for (Integer n : neighbors.get(label)) {
								propertypaths.PairInt next = new propertypaths.PairInt(n, etatSuivant.getHashCode());
								toProcess.addFirst(next);
							}
						}
					}
					// label est un inverse
					else if (label < 2 * getCharacterShift()) {
						int newlabel = label - getCharacterShift();
						if (invneighbors != null && invneighbors.get(newlabel) != null) {
							for (Integer n : invneighbors.get(newlabel)) {
								propertypaths.PairInt next = new propertypaths.PairInt(n, etatSuivant.getHashCode());
								toProcess.addFirst(next);
							}
						}
					}
					// negation (set)
					else {
						IntBooleanHashMap forbiddenOut = negationSets.get(label);
						IntBooleanHashMap forbiddenIn = negationSetsRev.get(label);
						if (!forbiddenOut.keySet().isEmpty() && neighbors != null) {
							MutableIntIterator a = neighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenOut.get(b)) {
									for (Integer n : neighbors.get(b)) {
										propertypaths.PairInt next = new propertypaths.PairInt(n,
												etatSuivant.getHashCode());
										toProcess.addFirst(next);
									}
								}

							}
						}
						if (!forbiddenIn.keySet().isEmpty() && invneighbors != null) {
							MutableIntIterator a = invneighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenIn.get(b + getCharacterShift())) {
									for (Integer n : invneighbors.get(b)) {
										propertypaths.PairInt next = new propertypaths.PairInt(n,
												etatSuivant.getHashCode());
										toProcess.addFirst(next);
									}
								}

							}
						}
					}
				}
			} else {
				for (Integer label : labels) {
					ArrayList<StateNode> etatsSuivants = etatCourant.getInNeighbors().get(label); //
					// System.out.println(">>> through " + label + " : " +
					// etatsSuivants);
					if (label < getCharacterShift()) {
						if (neighbors != null && neighbors.get(label) != null) {
							for (Integer n : neighbors.get(label)) {
								for (StateNode x : etatsSuivants) {
									propertypaths.PairInt next = new propertypaths.PairInt(n, x.getHashCode());
									toProcess.addFirst(next);
								}
							}
						}
					} else if (label < 2 * getCharacterShift()) {
						int newlabel = label - getCharacterShift();
						if (invneighbors != null && invneighbors.get(newlabel) != null) {
							for (Integer n : invneighbors.get(newlabel)) {
								for (StateNode x : etatsSuivants) {
									propertypaths.PairInt next = new propertypaths.PairInt(n, x.getHashCode());
									toProcess.addFirst(next);
								}
							}
						}
					} else {
						IntBooleanHashMap forbiddenOut = negationSets.get(label);
						IntBooleanHashMap forbiddenIn = negationSetsRev.get(label);
						// System.out.println(">>>> forbiddens : " +
						// forbiddenOut + ", " + forbiddenIn);
						if (!forbiddenOut.keySet().isEmpty() && neighbors != null) {
							MutableIntIterator a = neighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenOut.get(b)) {
									for (Integer n : neighbors.get(b)) {
										for (StateNode etatSuivant : etatsSuivants) {
											propertypaths.PairInt next = new propertypaths.PairInt(n,
													etatSuivant.getHashCode());
											toProcess.addFirst(next);
										}
									}
								}

							}
						}
						if (!forbiddenIn.keySet().isEmpty() && invneighbors != null) {
							MutableIntIterator a = invneighbors.keySet().intIterator();
							while (a.hasNext()) {
								int b = a.next();
								if (!forbiddenIn.get(b + getCharacterShift())) {
									for (Integer n : invneighbors.get(b)) {
										for (StateNode etatSuivant : etatsSuivants) {
											propertypaths.PairInt next = new propertypaths.PairInt(n,
													etatSuivant.getHashCode());
											toProcess.addFirst(next);
										}
									}
								}
							}
						}
					}
				}
			}
			if (!backward && etatCourant.isFinal()) {
				solutions.add(current.getLeft()); //
			} else if (backward && etatCourant.isInit()) {
				solutions.add(current.getLeft());
			}
		}
		return solutions;
	}

	public ArrayList<Integer> computeFrontCandidates(GraphAutomaton graph) {
		ArrayList<Integer> canFront = new ArrayList<>();
		IntBooleanHashMap seenFront = new IntBooleanHashMap();
		StateNode start = graph.getInitialState();
		if (start.isFinal()) {
			MutableIntIterator i = int2stringSO.keySet().intIterator();
			while (i.hasNext()) {
				Integer n = i.next();
				canFront.add(n);
				seenFront.put(n, true);
			}
		}
		for (Integer label : start.getOutLabels()) {
			if (label < getCharacterShift()) {
				if (predicates_index_out.get(label) != null) {
					for (Integer i : predicates_index_out.get(label)) {
						if (!seenFront.get(i)) {
							canFront.add(i);
							seenFront.put(i, true);
						}
					}
				}
			} else if (label < 2 * getCharacterShift()) {
				if (predicates_index_in.get(label - getCharacterShift()) != null) {
					for (Integer i : predicates_index_in.get(label - getCharacterShift())) {
						if (!seenFront.get(i)) {
							canFront.add(i);
							seenFront.put(i, true);
						}
					}
				}
			} else {

				IntBooleanHashMap forbiddenOut = negationSets.get(label);
				IntBooleanHashMap forbiddenIn = negationSetsRev.get(label);
				if (!forbiddenOut.isEmpty()) {
					MutableIntIterator a = predicates_index_out.keySet().intIterator();
					while (a.hasNext()) {
						int b = a.next();
						if (!forbiddenOut.get(b)) {
							for (Integer i : predicates_index_out.get(b)) {
								if (!seenFront.get(i)) {
									canFront.add(i);
									seenFront.put(i, true);
								}
							}
						}
					}
				}
				if (!forbiddenIn.isEmpty()) {
					MutableIntIterator a = predicates_index_in.keySet().intIterator();
					while (a.hasNext()) {
						int b = a.next();
						if (!forbiddenIn.get(b + getCharacterShift())) {
							for (Integer i : predicates_index_in.get(b)) {
								if (!seenFront.get(i)) {
									canFront.add(i);
									seenFront.put(i, true);
								}
							}
						}
					}
				}
			}

		}
		return canFront;
	}

	public ArrayList<PairInt> computeBackCandidates(GraphAutomaton graph) {
		ArrayList<PairInt> canBack = new ArrayList<>();
		ObjectBooleanHashMap<PairInt> seenBack = new ObjectBooleanHashMap<>();
		ArrayList<StateNode> finalStates = graph.getFinalStates();
		for (StateNode f : finalStates) {
			if (f.isInit()) {
				MutableIntIterator i = int2stringSO.keySet().intIterator();
				while (i.hasNext()) {
					Integer n = i.next();

					PairInt toAdd = new PairInt(f.getHashCode(), n);

					canBack.add(toAdd);
					seenBack.put(toAdd, true);

				}
			}
			for (Integer label : f.getInLabels()) {
				if (label < getCharacterShift()) {
					if (predicates_index_in.get(label) != null) {
						for (Integer i : predicates_index_in.get(label)) {
							PairInt toAdd = new PairInt(f.getHashCode(), i);
							if (!seenBack.get(toAdd)) {
								canBack.add(toAdd);
								seenBack.put(toAdd, true);

							}
						}
					}

				} else if (label < 2 * getCharacterShift()) {
					if (predicates_index_out.get(label - getCharacterShift()) != null) {
						for (Integer i : predicates_index_out.get(label - getCharacterShift())) {
							PairInt toAdd = new PairInt(f.getHashCode(), i);
							if (!seenBack.get(toAdd)) {
								canBack.add(toAdd);
								seenBack.put(toAdd, true);
							}
						}
					}
				} else {
					IntBooleanHashMap forbiddenOut = negationSets.get(label);
					IntBooleanHashMap forbiddenIn = negationSetsRev.get(label);
					if (!forbiddenOut.isEmpty()) {
						MutableIntIterator a = predicates_index_in.keySet().intIterator();
						while (a.hasNext()) {
							int b = a.next();
							if (!forbiddenOut.get(b)) {
								// System.out.println(predicates_index_in);
								for (Integer i : predicates_index_in.get(b)) {
									// System.out.println("coucou : " + i);
									PairInt toAdd = new PairInt(f.getHashCode(), i);
									if (!seenBack.get(toAdd)) {
										canBack.add(toAdd);
										seenBack.put(toAdd, true);
									}
								}
							}
						}
					}
					if (!forbiddenIn.isEmpty()) {
						MutableIntIterator a = predicates_index_out.keySet().intIterator();
						while (a.hasNext()) {
							int b = a.next();
							if (!forbiddenIn.get(b + getCharacterShift())) {
								for (Integer i : predicates_index_out.get(b)) {
									PairInt toAdd = new PairInt(f.getHashCode(), i);
									if (!seenBack.get(toAdd)) {
										canBack.add(toAdd);
										seenBack.put(toAdd, true);
									}
								}
							}
						}
					}
				}
			}

		}
		return canBack;
	}

	public void evaluateQueryLeaf(TreeLeaf leaf, boolean backward) {

		GraphAutomaton graph = leaf.getGraphAutomaton();

		ArrayList<PairInt> candidates = leaf.getCandidates();
		if (candidates != null && !candidates.isEmpty()) {

			ArrayList<PairInt> solutions = new ArrayList<>();

			HashMap<Integer, ArrayList<Integer>> realCandidates = computeStartCandidates(candidates);
			// System.out.println(">>Initial candidates : "
			// +startCandidates.size());
			// System.out.println(">> Filtered : "+realCandidates.size());
			for (Integer c : realCandidates.keySet()) {
				ArrayList<Integer> solTemp = null;
				if (leaf.isKleene() || leaf.getTree().isDistinct()) {
					solTemp = evaluateKleenex(leaf.getGraphAutomaton(), c,
							leaf.getGraphAutomaton().getInitialState().getHashCode(), false);
				} else {
					solTemp = evaluate(leaf.getGraphAutomaton(), c,
							leaf.getGraphAutomaton().getInitialState().getHashCode(), false);
				}
				for (Integer sol : solTemp) {
					for (Integer start : realCandidates.get(c)) {
						solutions.add(new PairInt(start, sol));
					}
				}
			}
			leaf.setCurrentSolutions(solutions);

		} else if (candidates == null) {
			ArrayList<PairInt> solutions = new ArrayList<>();
			if (leaf.getEndSelectivity() < leaf.getStartSelectivity() && leaf.getTree().hasDoubleVariable()) {
				ArrayList<PairInt> canBack = computeBackCandidates(graph);
				for (PairInt i : canBack) {
					if (leaf.isKleene() || leaf.getTree().isDistinct()) {
						ArrayList<Integer> solutionsGraph = evaluateKleenex(graph, i.getRight(), i.getLeft(), true);
						for (Integer sol : solutionsGraph)
							solutions.add(new PairInt(sol, i.getRight()));
					} else {
						ArrayList<Integer> solutionsGraph = evaluate(graph, i.getRight(), i.getLeft(), true);
						for (Integer sol : solutionsGraph)
							solutions.add(new PairInt(sol, i.getRight()));
					}
				}
			} else {
				ArrayList<Integer> canFront = new ArrayList<>();
				if (leaf.getTree().isFixedLeft()) {
					// System.out.println("Fixed Left");
					canFront.add(leaf.getTree().getFixedStart());
				} else {
					canFront = computeFrontCandidates(graph);
				}

				for (Integer i : canFront) {
					if (leaf.isKleene() || leaf.getTree().isDistinct()) {
						ArrayList<Integer> solutionsGraph = evaluateKleenex(graph, i,
								graph.getInitialState().getHashCode(), false);
						for (Integer sol : solutionsGraph)
							solutions.add(new PairInt(i, sol));
					} else {
						ArrayList<Integer> solutionsGraph = evaluate(graph, i, graph.getInitialState().getHashCode(),
								false);
						for (Integer sol : solutionsGraph)
							solutions.add(new PairInt(i, sol));
					}
				}
			}
			leaf.setCurrentSolutions(solutions);
			// System.out.println(">> " + current.getCurrentSolutions());

		}
	}

	public void evaluateQueryLeafQP(TreeLeaf leaf) {
		// System.out.println("> evaluating leaf : " + leaf.getRegex() + ", " +
		// leaf.getSelectivity());
		if (leaf.getStartCandidates() == null && leaf.getEndCandidates() == null) {
			// System.out.println("> No candidates at all");
			// System.out.println(leaf.getStartSelectivity() + " --- " +
			// leaf.getEndSelectivity());
			if (leaf.getEndSelectivity() < leaf.getStartSelectivity()) {
				// System.out.println("> Doing it backward");
				ArrayList<PairInt> candidates = computeBackCandidates(leaf.getGraphAutomaton());
				// System.out.println("> back candidates : " +
				// candidates.size());
				ArrayList<PairInt> solutions = new ArrayList<>();
				for (PairInt c : candidates) {
					if (leaf.isKleene() || leaf.getTree().isDistinct()) {
						ArrayList<Integer> solutionsKleene = evaluateKleenex(leaf.getGraphAutomaton(), c.getRight(),
								c.getLeft(), true);
						for (Integer s : solutionsKleene) {
							solutions.add(new PairInt(s, c.getRight()));
						}
					} else {
						ArrayList<Integer> solutionsNormal = evaluate(leaf.getGraphAutomaton(), c.getRight(),
								c.getLeft(), true);
						for (Integer s : solutionsNormal) {
							solutions.add(new PairInt(s, c.getRight()));
						}
					}
				}
				leaf.setCurrentSolutions(solutions);
			} else {
				// System.out.println("> Doing it frontward");
				ArrayList<Integer> candidates = computeFrontCandidates(leaf.getGraphAutomaton());
				ArrayList<PairInt> solutions = new ArrayList<>();
				for (Integer c : candidates) {
					if (leaf.isKleene() || leaf.getTree().isDistinct()) {
						ArrayList<Integer> solutionsKleene = evaluateKleenex(leaf.getGraphAutomaton(), c,
								leaf.getGraphAutomaton().getInitialState().getHashCode(), false);
						for (Integer s : solutionsKleene) {
							solutions.add(new PairInt(c, s));
						}
					} else {
						ArrayList<Integer> solutionsNormal = evaluate(leaf.getGraphAutomaton(), c,
								leaf.getGraphAutomaton().getInitialState().getHashCode(), false);
						for (Integer s : solutionsNormal) {
							solutions.add(new PairInt(c, s));
						}
					}
				}
				leaf.setCurrentSolutions(solutions);
			}

		} else if (leaf.getStartCandidates() != null) {
			// System.out.println("> Got startCandidates");
			ArrayList<PairInt> startCandidates = leaf.getStartCandidates();
			ArrayList<PairInt> solutions = new ArrayList<>();

			HashMap<Integer, ArrayList<Integer>> realCandidates = computeStartCandidates(startCandidates);
			// System.out.println(">>Initial candidates : "
			// +startCandidates.size());
			// System.out.println(">> Filtered : "+realCandidates.size());
			for (Integer c : realCandidates.keySet()) {
				ArrayList<Integer> solTemp = null;
				if (leaf.isKleene() || leaf.getTree().isDistinct()) {
					solTemp = evaluateKleenex(leaf.getGraphAutomaton(), c,
							leaf.getGraphAutomaton().getInitialState().getHashCode(), false);
				} else {
					solTemp = evaluate(leaf.getGraphAutomaton(), c,
							leaf.getGraphAutomaton().getInitialState().getHashCode(), false);
				}
				for (Integer sol : solTemp) {
					for (Integer start : realCandidates.get(c)) {
						solutions.add(new PairInt(start, sol));
					}
				}
			}
			leaf.setCurrentSolutions(solutions);
		} else if (leaf.getEndCandidates() != null) {
			// System.out.println("> Got endCandidates");
			ArrayList<PairInt> endCandidates = leaf.getEndCandidates();

			HashMap<Integer, ArrayList<Integer>> realCandidates = computeEndCandidates(endCandidates);
			// System.out.println("> leaf endCandidates # " +
			// endCandidates.size());
			ArrayList<PairInt> solutions = new ArrayList<>();
			// System.out.println("Initial candidates : " +
			// endCandidates.size());

			// System.out.println("Filtered candidates : " +
			// realCandidates.size());
			for (Integer c : realCandidates.keySet()) {
				// System.out.println(c);
				ArrayList<Integer> tempSol = new ArrayList<Integer>();
				ArrayList<StateNode> finalStates = computeFinalStateNodes(leaf.getGraphAutomaton(), c);
				if (leaf.isKleene() || leaf.getTree().isDistinct()) {
					for (StateNode finalState : finalStates) {

						tempSol.addAll(evaluateKleenex(leaf.getGraphAutomaton(), c, finalState.getHashCode(), true));
					}
				} else {
					for (StateNode finalState : finalStates) {
						tempSol.addAll(evaluate(leaf.getGraphAutomaton(), c, finalState.getHashCode(), true));
					}
				}
				for (Integer sol : tempSol) {
					for (Integer joint : realCandidates.get(c))
						solutions.add(new PairInt(sol, joint));
				}
			}

			leaf.setCurrentSolutions(solutions);
		} else {
			System.out.println("> Very bizarre");
		}
	}

	private HashMap<Integer, ArrayList<Integer>> computeStartCandidates(ArrayList<PairInt> startCandidates) {
		HashMap<Integer, ArrayList<Integer>> filtered = new HashMap<>();
		for (PairInt can : startCandidates) {
			if (filtered.get(can.getRight()) == null)
				filtered.put(can.getRight(), new ArrayList<Integer>());
			filtered.get(can.getRight()).add(can.getLeft());
		}
		return filtered;
	}

	private HashMap<Integer, ArrayList<Integer>> computeEndCandidates(ArrayList<PairInt> endCandidates) {
		HashMap<Integer, ArrayList<Integer>> filtered = new HashMap<>();
		for (PairInt can : endCandidates) {
			if (filtered.get(can.getLeft()) == null)
				filtered.put(can.getLeft(), new ArrayList<Integer>());
			filtered.get(can.getLeft()).add(can.getRight());
		}
		return filtered;
	}

	private ArrayList<StateNode> computeFinalStateNodes(GraphAutomaton automaton, Integer start) {
		ArrayList<StateNode> toReturn = new ArrayList<>();
		for (StateNode f : automaton.getFinalStates()) {
			if (f.isInit())
				toReturn.add(f);
			else {
				for (Integer label : f.getInLabels()) {
					if (fastInNeighbors.get(start) != null && fastInNeighbors.get(start).get(label) != null
							&& !fastInNeighbors.get(start).get(label).isEmpty()) {
						toReturn.add(f);
						break;
					}
				}
			}
		}
		return toReturn;
	}

	public void evaluateQueryTree(TreeNode node) {
		// System.out.println("evaluatin node " + node);

		// node.printCandidatesNumber();
		if (node.isLeaf()) {
			evaluateQueryLeaf((TreeLeaf) node, true);
		} else {
			if (node.getOperator() == OPERATOR.ALT) {
				if (node.getCandidates() != null) {
					node.getLeft().setCandidates(node.getCandidates());
					node.getRight().setCandidates(node.getCandidates());
				}
				evaluateQueryTree(node.getLeft());
				evaluateQueryTree(node.getRight());
				ArrayList<PairInt> alt = new ArrayList<>();
				alt.addAll(node.getLeft().getCurrentSolutions());
				alt.addAll(node.getRight().getCurrentSolutions());
				node.setCurrentSolutions(alt);
			} else if (node.getOperator() == OPERATOR.SEQ) {
				if (node.getCandidates() != null) {
					node.getLeft().setCandidates(node.getCandidates());
				}
				evaluateQueryTree(node.getLeft());
				ArrayList<PairInt> seq = new ArrayList<>();
				seq.addAll(node.getLeft().getCurrentSolutions());

				node.getRight().setCandidates(seq);
				evaluateQueryTree(node.getRight());

				node.setCurrentSolutions(node.getRight().getCurrentSolutions());
			} else {
				System.err.println("In evaluateQueryTree(TreeNode), this case should not occur...");
			}
		}
	}

	public void evaluateQueryTreeQP(TreeNode current) {
		if (current.isLeaf()) {
			evaluateQueryLeafQP((TreeLeaf) current);
			// System.out.println("leaf # solutions : " +
			// current.getCurrentSolutions().size());
		} else {
			if (current.getStartCandidates() != null) {
				// System.out.println("Got startCandidates to inject");
				current.getLeft().setStartCandidates(current.getStartCandidates());
				current.getRight().setStartCandidates(current.getStartCandidates());
			}
			if (current.getEndCandidates() != null) {

				// System.out.println("Got endCandidates to inject");
				current.getLeft().setEndCandidates(current.getEndCandidates());
				current.getRight().setEndCandidates(current.getEndCandidates());
			}

			if (current.getOperator() == OPERATOR.SEQ) {
				if (current.getStartCandidates() == null && current.getEndCandidates() == null) {
					// System.out.println("Got no candidates in this SEQ");
					TreeNode left = current.getLeft();
					TreeNode right = current.getRight();
					Long leftStart = left.getSelectivity();
					Long rightStart = right.getSelectivity();

					if (leftStart > rightStart) {
						// System.out.println("Better selectivity right ( " +
						// rightStart + " < " + leftStart + " )");
						// droite -> gauche
						TreeNode first = current.getRight();
						TreeNode second = current.getLeft();
						evaluateQueryTreeQP(first);
						second.setEndCandidates(first.getCurrentSolutions());
						// System.out.println("second has " +
						// second.getEndCandidates().size() + " endCandidates");
						evaluateQueryTreeQP(second);
						current.setCurrentSolutions(second.getCurrentSolutions());
					} else {

						// System.out.println("Better selectivity left ( " +
						// rightStart + " > " + leftStart + " )");
						// gauche -> droite
						TreeNode first = current.getLeft();
						TreeNode second = current.getRight();
						evaluateQueryTreeQP(first);
						second.setStartCandidates(first.getCurrentSolutions());
						evaluateQueryTreeQP(second);
						current.setCurrentSolutions(second.getCurrentSolutions());
					}
				} else if (current.getStartCandidates() != null) {
					// System.out.println("Because of startCandidates, doing
					// left first");
					TreeNode first = current.getLeft();
					TreeNode second = current.getRight();
					evaluateQueryTreeQP(first);
					second.setStartCandidates(first.getCurrentSolutions());
					evaluateQueryTreeQP(second);
					current.setCurrentSolutions(second.getCurrentSolutions());
				} else if (current.getEndCandidates() != null) {
					// System.out.println("Because of endCandidates, doing right
					// first");
					TreeNode first = current.getRight();
					TreeNode second = current.getLeft();
					evaluateQueryTreeQP(first);
					second.setEndCandidates(first.getCurrentSolutions());
					evaluateQueryTreeQP(second);

					current.setCurrentSolutions(second.getCurrentSolutions());
				} else if (current.getStartCandidates() != null && current.getEndCandidates() != null) {
					// System.out.println("Etrange !");
				}
			} else if (current.getOperator() == OPERATOR.ALT) {
				evaluateQueryTreeQP(current.getLeft());
				evaluateQueryTreeQP(current.getRight());
				ArrayList<PairInt> alt = new ArrayList<>();
				alt.addAll(current.getLeft().getCurrentSolutions());
				alt.addAll(current.getRight().getCurrentSolutions());

				current.setCurrentSolutions(alt);
			} else {
				System.err.println("In evaluateQueryTreeQP(TreeNode), this case should not occur.");
			}
		}

	}

	/**
	 * Checks if 2 nodes are connected, with respect to all the dimensions they
	 * must share.
	 * 
	 * @param node1
	 * @param node2
	 * @param dimensions
	 * @param direction
	 * @return
	 */
	public boolean checkIfNeighExists(Integer node1, Integer node2, short[] dimensions, Integer direction) {
		// System.out.println("Calling checkIf for nodes : " + node1 + " and " +
		// node2 + ", with dims :" + dimensions
		// + " and direction " + direction);
		return query(node1, dimensions, direction).contains(node2);
	}

	/**
	 * Returns the set of graph nodes that are connected to this vertex by all
	 * the given dimensions.
	 * 
	 * @param node
	 * @param dimensions
	 * @return
	 */
	public ArrayList<Integer> query(Integer node, short[] dimensions, Integer direction) {
		// System.out.println(
		// "Calling query for node : " + node + ", with dims :" + dimensions + "
		// and direction " + direction);
		ArrayList<Integer> temp = new ArrayList<>(Settings.ARRAY_SIZE);
		if (direction == Settings.IN) {
			IntObjectHashMap<ArrayList<Integer>> in = fastInNeighbors.get(node);
			if (in != null) {
				ArrayList<Integer> neighs = in.get((int) dimensions[0]);
				if (neighs != null) {
					for (Integer n : neighs) {
						temp.add(n);
					}

					// intersection with the rest of the dimensions
					for (int i = 1; i < dimensions.length; i++) {
						neighs = in.get((int) dimensions[i]);
						temp.retainAll(neighs);
					}
				}
			}
		} else {
			IntObjectHashMap<ArrayList<Integer>> out = fastOutNeighbors.get(node);
			if (out != null) {
				ArrayList<Integer> neighs = out.get((int) dimensions[0]);
				if (neighs != null) {
					for (Integer n : neighs) {
						temp.add(n);
					}

					// intersection with the rest of the dimensions
					for (int i = 1; i < dimensions.length; i++) {
						neighs = out.get((int) dimensions[i]);
						temp.retainAll(neighs);
					}
				}
			}
		}
		return temp;
	}

	public IntObjectHashMap<ArrayList<Integer>> getPredsOut(int node) {
		return fastOutNeighbors.get(node);
	}

	public IntObjectHashMap<ArrayList<Integer>> getPredsIn(int node) {
		return fastInNeighbors.get(node);
	}

	public String convertIntToStringP(int charValue) {
		return (String) int2stringP.get(charValue);
	}

	public String convertIntToStringSO(Integer right) {

		return (String) int2stringSO.get(right);
	}

	public Long getNodesCount() {
		return new Long(int2stringSO.size());
	}

	public IntObjectHashMap getInt2StringSO() {
		return int2stringSO;
	}

	public ObjectIntHashMap<String> getString2ShortP() {
		return this.string2IntP;
	}

	public ObjectIntHashMap<String> getString2intSO() {
		return string2intSO;
	}

	public IntObjectHashMap getInt2stringSO() {
		return int2stringSO;
	}

	public IntObjectHashMap getInt2stringP() {
		return int2stringP;
	}

}
