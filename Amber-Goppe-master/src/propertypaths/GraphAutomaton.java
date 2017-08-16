package propertypaths;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Stack;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.State;
import dk.brics.automaton.Transition;

public class GraphAutomaton {

	private StateNode initialState;
	private HashMap<Integer, StateNode> states;
	private ArrayList<StateNode> finalStates;

	/**
	 * Parcours en profondeur de l'automate de l'expression régulière. Crée un
	 * graphe navigable à partir d'un automate d'une expression régulière.
	 * 
	 * @param a
	 * @param pp
	 */
	public GraphAutomaton(Automaton a) {
		states = new HashMap<>();
		State init = a.getInitialState();
		finalStates = new ArrayList<>();
		int id = 0;
		// System.out.println("Bricks final stats : "+a.getAcceptStates());
		HashMap<State, Boolean> visited = new HashMap<>();
		Stack<State> toVisit = new Stack<>();

		// Ajout de l'état initial à la pile de noeuds à visiter
		toVisit.push(init);
		// System.out.println(a);
		// Tant qu'il reste des états à visiter
		while (!toVisit.empty()) {
			// On prend le premier de la pile et on le marque visité
			State current = toVisit.pop();
			visited.put(current, true);

			// On crée ou on récupère le noeud du Graphe associé à cet état
			// On les identifie via leur hashcode.
			StateNode currentNode;
			if (states.get(current.hashCode()) != null) {
				currentNode = states.get(current.hashCode());
			} else {
				boolean isInit = false;
				if (id == 0)
					isInit = true;
				currentNode = new StateNode(isInit, current.isAccept(), current.hashCode(), id);
				id++;
				states.put(currentNode.getHashCode(), currentNode);
				if (isInit) {
					this.initialState = currentNode;
				}
			}
			if (current.isAccept()) {
				this.finalStates.add(currentNode);
			}
			// System.out.println("Current state : " + currentNode.getId() + ",
			// final : " + currentNode.isFinal());

			// Pour chaque transition sortante de cet état, il y aura un noeud
			// voisin du noeud courant dans le graphe.
			for (Transition t : current.getTransitions()) {
				State dest = t.getDest();
				StateNode destNode;
				// On créé ou récupère le noeud du graphe pour ce voisin.
				if (states.get(dest.hashCode()) != null)
					destNode = states.get(dest.hashCode());
				else {
					destNode = new StateNode(false, dest.isAccept(), dest.hashCode(), id);
					id++;
					states.put(destNode.getHashCode(), destNode);
				}
				// On récupère le label sur la transition
				// Les transitions sont codées par intervalles, il peut y avoir
				// plusieurs labels sur une transition [a,d] -> {a,b,c,d}
				Character min = t.getMin();
				Character max = t.getMax();
				if (min.equals(max)) {
					int l = min.charValue();
					currentNode.addOutNeighbor(l, destNode);
					destNode.addInNeighbor(l, currentNode);
					// System.out.println("\t" + l + " -> " + destNode.getId());
				} else {
					int minInt = (int) min;
					int maxInt = (int) max;
					for (int i = minInt; i <= maxInt; i++) {
						currentNode.addOutNeighbor(i, destNode);
						destNode.addInNeighbor(i, currentNode);
						// System.out.println("\t" + i + " -> " +
						// destNode.getId());
					}
				}

				// Si le voisin trouvé n'est pas dans la liste des visités, on
				// l'ajoute à la liste à visiter et on le marque visité
				if (visited.get(dest) == null) {
					toVisit.push(dest);
					visited.put(dest, true);
				}
			}
		}
	}

	public StateNode getInitialState() {
		return this.initialState;
	}

	public ArrayList<StateNode> getFinalStates() {
		return this.finalStates;
	}

	public HashMap<Integer, StateNode> getStates() {
		return this.states;
	}
}
