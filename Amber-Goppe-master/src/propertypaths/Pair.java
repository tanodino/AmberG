package propertypaths;

import java.util.Objects;

public class Pair<L, R> {
	private L left;
	private R right;

	public Pair(L left, R right) {
		this.left = left;
		this.right = right;
	}

	public Pair() {
		// TODO Auto-generated constructor stub
	}

	public L getLeft() {
		return left;
	}

	public R getRight() {
		return right;
	}

	public void setLeft(L left) {
		this.left = left;
	}

	public void setRight(R right) {
		this.right = right;
	}

	@Override
	public int hashCode() {
		return Objects.hash(left, right);
	}

	@SuppressWarnings("rawtypes")
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Pair))
			return false;
		Pair pairo = (Pair) o;
		return this.left.equals(pairo.getLeft()) && this.right.equals(pairo.getRight());
	}

	public String toString() {
		return "(" + left + ", " + right + ")";
	}

}