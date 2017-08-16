package propertypaths;

import java.util.ArrayList;
import java.util.Stack;

public class QueryTree {

	private TreeNode root = null;
	private TreeNode current = null;
	private boolean fused = false;
	private boolean doubleVariable = true;
	private boolean fixedLeft = false;
	private int fixedStart = 0;
	private boolean distinct = false;
	private ArrayList<Short> startLabels = new ArrayList<>();
	private GraphAutomaton originalAutomaton = null;
	private String initalPP = null;

	/**
	 * Method called when the Jena Parser is used. Builds the Query Tree of a PP
	 * while the query is parsed.
	 * 
	 * @param n
	 * @return
	 */
	public QueryTree add(TreeNode n) {
		// if (current != null)
		// System.out.println("current node : " + current + " son : " +
		// current.getSon());

		// System.out.println("adding binary node : " + n);
		if (getRoot() == null) {
			setRoot(n);
			n.setParent(n);
			n.setRoot(true);
			setCurrent(getRoot());
		} else {
			current.add(n);
			current = n;
		}
		return this;
	}

	public QueryTree add(TreeLeaf l) {
		if (getRoot() == null) {
			setRoot(l);
			l.setParent(l);
			l.setRoot(true);
			setCurrent(getRoot());
		}

		// if (current != null)
		// System.out.println("current node : " + current + " son : " +
		// current.getSon());

		// System.out.println("adding unary : " + l);
		current.add(l);
		while ((current.getSon() == 2 && !current.isRoot())
				|| (current.getSon() == 1 && current.getOperator() == OPERATOR.INV && !current.isRoot())) {
			// System.out.println(current);
			current = current.getParent();
			// System.out.println("backtracking to node : " + current + " son :
			// " + current.getSon());
		}
		return this;
	}

	public QueryTree fuseGroups() {
		this.root = fuse(root);
		this.fused = true;
		return this;
	}

	/**
	 * Fuse the Query Tree wrt the semantics.
	 * @param root
	 * @return
	 */
	public TreeNode fuse(TreeNode root) {
		if (!root.isLeaf()) {
			if (root.getOperator() == OPERATOR.INV) {
				TreeNode son = root.getLeft();
				TreeNode parent = root.getParent();
				if (son.isLeaf()) {
					TreeLeaf newson = new TreeLeaf(son.getOperator(),
							new Inverser("^" + ((TreeLeaf) son).getRegex()).getInversed(), this);

					if (parent.getLeft() == root) {
						parent.setLeft(newson);
						newson.setParent(parent);
					} else if (parent.getRight() == root) {
						parent.setRight(newson);
						newson.setParent(parent);
					} else
						setRoot(newson);
					return newson;
				}
				return null;
			} else {

				TreeNode left = fuse(root.getLeft());
				TreeNode right = fuse(root.getRight());
				if (left.isLeaf() && right.isLeaf()) {
					TreeLeaf newleft = (TreeLeaf) left;
					TreeLeaf newright = (TreeLeaf) right;
					if ((!newleft.isKleene() && !newright.isKleene())) {
						TreeLeaf fuse = fuseLeaves(newleft, root.getOperator(), newright);
						TreeNode parent = root.getParent();
						if (parent.getLeft() == root) {
							parent.setLeft(fuse);
							fuse.setParent(parent);
						} else if (parent.getRight() == root) {
							parent.setRight(fuse);
							fuse.setParent(parent);
						} else
							setRoot(fuse);
						return fuse;
					} else {
						return root;
					}
				} else {
					return root;
				}
			}
		} else {
			return root;
		}

	}

	public TreeLeaf fuseLeaves(TreeLeaf left, OPERATOR op, TreeLeaf right) {
		TreeLeaf fused = new TreeLeaf(OPERATOR.Link, "(" + left.getRegex() + op.asChar() + right.getRegex() + ")",
				this);
		return fused;
	}

	public TreeNode getCurrent() {
		return current;
	}

	public void setCurrent(TreeNode current) {
		this.current = current;
	}

	public TreeNode getRoot() {
		return root;
	}

	public void setRoot(TreeNode root) {
		this.root = root;
	}

	public boolean isFused() {
		return fused;
	}

	public void print() {
		Stack<Pair<TreeNode, Integer>> toVisit = new Stack<>();
		toVisit.push(new Pair<TreeNode, Integer>(getRoot(), 1));

		while (!toVisit.isEmpty()) {
			Pair<TreeNode, Integer> current = toVisit.pop();
			if (current.getLeft().isLeaf) {
				System.out.println(new String(new char[current.getRight()]).replace("\0", "-") + " "
						+ ((TreeLeaf) current.getLeft()).getRegex() + " : " + current.getLeft().getSelectivity());
			} else {
				System.out.println(new String(new char[current.getRight()]).replace("\0", "-") + " "
						+ current.getLeft().getOperator().asChar());
				if (current.getLeft().getOperator() != OPERATOR.INV)
					toVisit.add(new Pair<TreeNode, Integer>(current.getLeft().getRight(), current.getRight() + 1));
				toVisit.add(new Pair<TreeNode, Integer>(current.getLeft().getLeft(), current.getRight() + 1));
			}
		}
	}

	public void setFixedStart(int start) {
		this.fixedStart = start;
	}

	public int getFixedStart() {
		return this.fixedStart;
	}

	public void setFixedLeft() {
		this.doubleVariable = false;
		this.fixedLeft = true;
	}

	public boolean isFixedLeft() {
		return fixedLeft;
	}

	public boolean hasDoubleVariable() {
		return this.doubleVariable;
	}

	public ArrayList<TreeLeaf> getLeaves() {
		Stack<TreeNode> toVisit = new Stack<>();
		toVisit.push(getRoot());
		ArrayList<TreeLeaf> toRet = new ArrayList<>();
		while (!toVisit.isEmpty()) {
			TreeNode current = toVisit.pop();
			if (current.isLeaf()) {
				toRet.add((TreeLeaf) current);
			} else {
				if (current.getOperator() != OPERATOR.INV)
					toVisit.add(current.getRight());
				toVisit.add(current.getLeft());
			}
		}
		return toRet;
	}

	public void setDistinct(boolean b) {
		this.distinct = true;
	}

	public boolean isDistinct() {
		return this.distinct;
	}

	public void computeSelectivity(TreeNode current) {
		if (current.isLeaf) {
			TreeLeaf leaf = (TreeLeaf) current;
			leaf.computeSelectivity();
		} else {
			computeSelectivity(current.getLeft());
			computeSelectivity(current.getRight());
			long sel = 0L;
			if (current.getOperator() == OPERATOR.SEQ) {
				sel = Math.min(current.getLeft().getSelectivity(), current.getRight().getSelectivity());

			} else {
				sel = current.getLeft().getSelectivity() + current.getRight().getSelectivity();
			}
			current.setSelectivity(sel);
		}
	}

	/**
	 * Add a outgoing transition for the whole property path.
	 * 
	 * @param m
	 */
	public void addStartLabel(short m) {
		startLabels.add(m);
	}

	public ArrayList<Short> getStartLabels() {
		return startLabels;
	}

	public void setOriginalAutomaton(GraphAutomaton ga) {
		originalAutomaton = ga;
	}

	public GraphAutomaton getOriginalAutomaton() {
		return this.originalAutomaton;
	}

	public void setInitialPP(String pp) {
		this.initalPP = pp;
	}

	public String getInitialPP() {
		return this.initalPP;
	}

	public String toString() {
		return this.initalPP;
	}
}
