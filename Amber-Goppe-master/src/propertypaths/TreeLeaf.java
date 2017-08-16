package propertypaths;

import java.util.ArrayList;
import java.util.TreeSet;

import com.gs.collections.api.iterator.MutableIntIterator;
import com.gs.collections.impl.map.mutable.primitive.IntBooleanHashMap;

import data.GoppeGraphDatabase;
import dk.brics.automaton.Automaton;
import dk.brics.automaton.RegExp;

public class TreeLeaf extends TreeNode {

	private String regex = "";
	private GraphAutomaton ga = null;

	public TreeLeaf(OPERATOR o, String r, QueryTree qt) {
		super(o, qt);
		isLeaf = true;
		setRegex(r);
	}

	public TreeLeaf() {
		super();
	}

	public String toString() {
		return this.getOperator() + " " + getRegex();
	}

	public String getRegex() {
		return this.regex;
	}

	public boolean isKleene() {
		return !(this.getOperator() == OPERATOR.Link) && !(this.getOperator() == OPERATOR.NEG);
	}

	public void setRegex(String regex) {
		this.regex = regex;
	}

	/**
	 * Computes the selectivity of the Query Nodes, and generates their
	 * automata.
	 */
	public void computeSelectivity() {
		PPSolver solv = new PPSolver(this.getRegex());
		RegExp r = new RegExp(solv.getRegex());
		Automaton a = r.toAutomaton();
		a.determinize();
		ga = new GraphAutomaton(a);

		Long selectivityStart = 0L;
		Long selectivityEnd = 0L;

		StateNode start = ga.getInitialState();
		if (start.isFinal()) {
			selectivityStart = GoppeGraphDatabase.getDatabase().getNodesCount();
			selectivityEnd = GoppeGraphDatabase.getDatabase().getNodesCount();
		} else {
			for (Integer label : start.getOutLabels()) {
				int newlabel = label;
				if (label < GoppeGraphDatabase.getDatabase().getCharacterShift()) {
					if (GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().get(label) != null) {
						selectivityStart += GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().get(label).size();
					}

				} else if (label < 2 * GoppeGraphDatabase.getDatabase().getCharacterShift()) {
					newlabel = label - GoppeGraphDatabase.getDatabase().getCharacterShift();
					if (GoppeGraphDatabase.getDatabase().getPredicatesIndexIn().get(newlabel) != null) {
						selectivityStart += GoppeGraphDatabase.getDatabase().getPredicatesIndexIn().get(newlabel)
								.size();
					}

				} else {
					selectivityStart += GoppeGraphDatabase.getDatabase().getNodesCount();
				}
			}

			ArrayList<StateNode> finalStates = ga.getFinalStates();
			for (StateNode f : finalStates) {
				for (Integer label : f.getInLabels()) {
					int newlabel = label;
					if (label < GoppeGraphDatabase.getDatabase().getCharacterShift()) {
						if (GoppeGraphDatabase.getDatabase().getPredicatesIndexIn().get(label) != null) {
							selectivityEnd += GoppeGraphDatabase.getDatabase().getPredicatesIndexIn().get(label).size();
						}

					} else if (label < 2 * GoppeGraphDatabase.getDatabase().getCharacterShift()) {
						newlabel = label - GoppeGraphDatabase.getDatabase().getCharacterShift();
						if (GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().get(newlabel) != null) {
							selectivityEnd += GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().get(newlabel)
									.size();
						}

					} else {
						selectivityEnd += GoppeGraphDatabase.getDatabase().getNodesCount();
					}
				}
			}
		}
		setStartSelectivity(selectivityStart);
		setEndSelectivity(selectivityEnd);

		long min = Long.MAX_VALUE;
		for (StateNode s : this.ga.getStates().values()) {
			if (s.isFinal() && s.isInit()) {
				min = GoppeGraphDatabase.getDatabase().getNodesCount();
				break;
			}
			long acc = 0;
			for (int l : s.getOutLabels()) {
				// System.out.println(l);
				if (l < GoppeGraphDatabase.getDatabase().getCharacterShift()) {
					TreeSet<Integer> neigh = GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().get(l);
					acc += (neigh == null) ? 0L : neigh.size();
				} else if (l < 2 * GoppeGraphDatabase.getDatabase().getCharacterShift()) {
					TreeSet<Integer> neigh = GoppeGraphDatabase.getDatabase().getPredicatesIndexIn()
							.get(l - GoppeGraphDatabase.getDatabase().getCharacterShift());
					acc += (neigh == null) ? 0L : neigh.size();
				} else {
					IntBooleanHashMap forbiddenOut = GoppeGraphDatabase.getDatabase().getNegationSet(l);
					IntBooleanHashMap forbiddenIn = GoppeGraphDatabase.getDatabase().getNegationSetRev(l);
					if (!forbiddenOut.isEmpty()) {
						MutableIntIterator x = GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().keySet()
								.intIterator();
						while (x.hasNext()) {
							int b = x.next();
							if (!forbiddenOut.get(b)) {
								acc += GoppeGraphDatabase.getDatabase().getPredicatesIndexOut().get(b).size();
							}
						}
					}
					if (!forbiddenIn.isEmpty()) {
						MutableIntIterator x = GoppeGraphDatabase.getDatabase().getPredicatesIndexIn().keySet()
								.intIterator();
						while (x.hasNext()) {
							int b = x.next();
							if (!forbiddenIn.get(b + GoppeGraphDatabase.getDatabase().getCharacterShift())) {
								acc += GoppeGraphDatabase.getDatabase().getPredicatesIndexIn().get(b).size();
							}
						}
					}
				}
			}
			if (min > acc && s.getOutLabels() != null && !s.getOutLabels().isEmpty()) {
				min = acc;
			}
		}
		// System.out.println("Leaf selectivity " + this.getRegex() + " : " +
		// min);
		this.selectivity = min;
	}

	public GraphAutomaton getGraphAutomaton() {
		return this.ga;
	}
}
