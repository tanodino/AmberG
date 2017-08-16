package propertypaths;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;

public class StateNode {

	private int hashCode;
	private int id;
	private boolean isInit = false;
	private boolean isFinal = false;
	private HashMap<Integer, StateNode> outNeighbors;
	private HashMap<Integer, ArrayList<StateNode>> inNeighbors;

	public StateNode(boolean isInit, boolean isFinal, int hashCode, int id) {
		this.isInit = isInit;
		this.isFinal = isFinal;
		this.hashCode = hashCode;
		this.outNeighbors = new HashMap<>();
		this.inNeighbors = new HashMap<>();
		this.id = id;
	}

	public StateNode addOutNeighbor(int s, StateNode n) {
		if (outNeighbors.get(s) == null) {
			outNeighbors.put(s, n);
		}
		return this;
	}

	public StateNode addInNeighbor(int s, StateNode n) {
		if (inNeighbors.get(s) == null) {
			inNeighbors.put(s, new ArrayList<StateNode>());
		}
		inNeighbors.get(s).add(n);
		return this;
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof StateNode))
			return false;
		StateNode pairo = (StateNode) o;
		return this.id == pairo.id;
	}

	public int getId() {
		return id;
	}

	public boolean isInit() {
		return isInit;
	}

	public boolean isFinal() {
		return isFinal;
	}

	public int getHashCode() {
		return hashCode;
	}

	public HashMap<Integer, StateNode> getOutNeighbors() {
		return outNeighbors;
	}

	public HashMap<Integer, ArrayList<StateNode>> getInNeighbors() {
		return inNeighbors;
	}

	public Set<Integer> getOutLabels() {
		return outNeighbors.keySet();
	}

	public Set<Integer> getInLabels() {
		return inNeighbors.keySet();
	}

	public String toString() {
		return String.valueOf(this.hashCode);
	}
}
