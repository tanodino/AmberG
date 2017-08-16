package query;

import java.util.ArrayList;

import propertypaths.QueryTree;

public class PPLinkPath extends LinkObjectPath {
	public ArrayList<QueryTree> pps;

	public PPLinkPath(int previous_id, int rank_previous_id, int direction, ArrayList<QueryTree> pps) {
		super(previous_id, rank_previous_id, direction);
		this.pps = pps;
		this.linkType = 1;
	}

	public String toString() {
		return "RANK Prev ID: " + rank_previous_id + " DIR: " + direction + " PP: " + pps;
	}

	public int size() {
		return 0;
	}
}
