package query;

import java.util.Arrays;

public class NormalLinkPath extends LinkObjectPath {
	public short[] dims;

	public NormalLinkPath(int previous_id, int rank_previous_id, int direction, short[] dims) {
		super(previous_id, rank_previous_id, direction);
		this.dims = dims;
		this.linkType = 0;
	}

	public String toString() {
		return "RANK Prev ID: " + rank_previous_id + " DIR: " + direction + " DIM: " + Arrays.toString(dims);
	}

	public int size() {
		return dims.length;
	}
}
