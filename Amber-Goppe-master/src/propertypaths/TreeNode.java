package propertypaths;

import java.util.ArrayList;

public class TreeNode {
	protected boolean isLeaf = false;
	private boolean isRoot = false;
	private OPERATOR op = null;
	private TreeNode left = null;
	private TreeNode right = null;
	private TreeNode parent = null;
	private int son = 0;
	private QueryTree tree = null;

	private ArrayList<PairInt> currentSolutions = new ArrayList<>();
	private ArrayList<PairInt> candidates = null;

	private Long startSelectivity = 0L;
	private Long endSelectivity = 0L;

	private ArrayList<PairInt> startCandidates = null;
	private ArrayList<PairInt> endCandidates = null;
	protected long selectivity = 0L;

	protected TreeNode() {
	}

	public TreeNode(OPERATOR o, QueryTree qt) {
		this.op = o;
		this.tree = qt;
	}

	public TreeNode(OPERATOR o, String left, String right, QueryTree qt) {
		this(o, qt);
	}

	public TreeNode add(TreeNode n) {

		if (this.son == 0) {
			// System.out.println("added left");
			addLeft(n);
		} else {
			// System.out.println("added right");
			addRight(n);
		}
		return this;
	}

	public TreeNode getLeft() {
		return left;
	}

	protected void setLeft(TreeNode left) {
		this.left = left;
	}

	public TreeNode getRight() {
		return right;
	}

	protected void setRight(TreeNode right) {
		this.right = right;
	}

	private TreeNode addLeft(TreeNode l) {
		this.setLeft(l);
		l.setParent(this);
		this.son++;
		// System.out.println("next son should be right (" + this.son + ")");
		return this;
	}

	private TreeNode addRight(TreeNode r) {
		this.setRight(r);
		r.setParent(this);
		this.son++;
		// System.out.println("should backtrack (" + this.son + ")");
		return this;
	}

	public TreeNode getParent() {
		return parent;
	}

	public void setParent(TreeNode parent) {
		this.parent = parent;
	}

	public OPERATOR getOperator() {
		return this.op;
	}

	public boolean isLeaf() {
		return isLeaf;
	}

	public boolean isRoot() {
		return isRoot;
	}

	public void setRoot(boolean r) {
		isRoot = r;
	}

	public int getSon() {
		return son;
	}

	public void setSon(int son) {
		this.son = son;
	}

	public ArrayList<PairInt> getCurrentSolutions() {
		return currentSolutions;
	}

	public void setCurrentSolutions(ArrayList<PairInt> currentSolutions) {
		this.currentSolutions = currentSolutions;
	}

	public ArrayList<PairInt> getCandidates() {
		return candidates;
	}

	public void setCandidates(ArrayList<PairInt> alt) {
		this.candidates = alt;
	}

	public QueryTree getTree() {
		return this.tree;
	}

	public Long getEndSelectivity() {
		return endSelectivity;
	}

	public void setEndSelectivity(Long endCandidatesNumber) {
		this.endSelectivity = endCandidatesNumber;
	}

	public Long getStartSelectivity() {
		return startSelectivity;
	}

	public void setStartSelectivity(Long startCandidatesNumber) {
		this.startSelectivity = startCandidatesNumber;
	}

	public void printCandidatesNumber() {
		System.out.println("current StartC : " + this.getStartSelectivity());
		System.out.println("current EndC : " + this.getEndSelectivity());
		if (!isLeaf) {
			System.out.println("left StartC : " + this.getLeft().getStartSelectivity());
			System.out.println("left EndC : " + this.getLeft().getEndSelectivity());
			System.out.println("right StartC : " + this.getRight().getStartSelectivity());
			System.out.println("right EndC : " + this.getRight().getEndSelectivity());
		}

	}

	public ArrayList<PairInt> getStartCandidates() {
		return startCandidates;
	}

	public void setStartCandidates(ArrayList<PairInt> startCandidates) {
		this.startCandidates = startCandidates;
	}

	public ArrayList<PairInt> getEndCandidates() {
		return endCandidates;
	}

	public void setEndCandidates(ArrayList<PairInt> endCandidates) {
		this.endCandidates = endCandidates;
	}

	public long getSelectivity() {
		return this.selectivity;
	}

	public void setSelectivity(long sel) {
		this.selectivity = sel;

	}
}
