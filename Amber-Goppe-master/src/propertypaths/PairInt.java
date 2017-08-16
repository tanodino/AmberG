package propertypaths;

import java.util.Objects;

public class PairInt implements Comparable {
	private int left;
	private int right;
	private int hashCode;

	public PairInt(int left, int right) {
		this.left = left;
		this.right = right;
		this.hashCode = Objects.hash(left, right);
	}

	public PairInt() {
		// TODO Auto-generated constructor stub
	}

	public int getLeft() {
		return left;
	}

	public int getRight() {
		return right;
	}

	public void setLeft(int left) {
		this.left = left;
	}

	public void setRight(int right) {
		this.right = right;
	}

	@Override
	public int hashCode() {
		return hashCode;
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof PairInt))
			return false;
		PairInt pairo = (PairInt) o;
		return this.left == pairo.getLeft() && this.right == pairo.getRight();
	}

	public String toString() {
		return "(" + left + ", " + right + ")";
	}

	@Override
	public int compareTo(Object o) {
		if (!(o instanceof PairInt))
			return -1;

		PairInt pairo = (PairInt) o;
		return (this.left > pairo.getLeft()) ? 1 : (this.left < pairo.getLeft()) ? -1 : 0;
	}

}