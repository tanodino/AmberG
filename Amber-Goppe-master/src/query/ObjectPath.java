package query;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

import com.gs.collections.api.iterator.MutableIntIterator;
import com.gs.collections.impl.map.mutable.primitive.IntObjectHashMap;

import data.Settings;
import propertypaths.QueryTree;

public class ObjectPath {
	public int id;
	public int ranking_pos;
	public ArrayList<LinkObjectPath> previous_links_cores;
	public ArrayList<LinkObjectPath> selfLoop;
	public boolean isLiteralOrUri;
	public int literalOrUriCode;
	public IntObjectHashMap<LinkObjectPath> satellites_in; // source ->
															// {predicates}
	public IntObjectHashMap<LinkObjectPath> satellites_out; // target ->
															// {predicates}

	public ObjectPath(int id, int rank_pos) {
		this.id = id;
		this.ranking_pos = rank_pos;
		previous_links_cores = new ArrayList<LinkObjectPath>();
		selfLoop = null;
		isLiteralOrUri = false;
		literalOrUriCode = Settings.VARIABLE;
		satellites_in = new IntObjectHashMap<>();
		satellites_out = new IntObjectHashMap<>();
	}

	public void addSelfLoopPP(ArrayList<QueryTree> pps) {
		if (this.selfLoop == null)
			selfLoop = new ArrayList<>();
		selfLoop.add(new PPLinkPath(id, ranking_pos, Settings.OUT, pps));
	}

	public void addSelfLoopNormal(short[] dims) {
		if (this.selfLoop == null)
			selfLoop = new ArrayList<>();
		selfLoop.add(new NormalLinkPath(id, ranking_pos, Settings.OUT, dims));
	}

	public void addNormalSatelliteIn(int sat, short[] dims) {
		satellites_in.put(sat, new NormalLinkPath(id, ranking_pos, Settings.IN, dims));
	}

	public void addNormalSatelliteOut(int sat, short[] dims) {
		satellites_out.put(sat, new NormalLinkPath(id, ranking_pos, Settings.IN, dims));
	}

	public void addPPSatelliteIn(int sat, ArrayList<QueryTree> pps) {
		satellites_in.put(sat, new PPLinkPath(id, ranking_pos, Settings.IN, pps));
	}

	public void addPPSatelliteOut(int sat, ArrayList<QueryTree> pps) {
		satellites_out.put(sat, new PPLinkPath(id, ranking_pos, Settings.OUT, pps));
	}

	public void addNormalLink(int previous_id, int rank_previous_id, int direction, short[] dims) {
		previous_links_cores.add(new NormalLinkPath(previous_id, rank_previous_id, direction, dims));
	}

	public void addPPLink(int previous_id, int rank_previous_id, int direction, ArrayList<QueryTree> pp) {
		previous_links_cores.add(new PPLinkPath(previous_id, rank_previous_id, direction, pp));
	}

	public void sort() {
		Collections.sort(previous_links_cores);
	}

	public String toString() {
		String st = "id: " + id + " ranking_pos: " + ranking_pos + "\n";
		for (LinkObjectPath p : previous_links_cores) {
			st += "\t" + p.toString() + "\n";
		}
		if (selfLoop != null)
			st += "selfloop: " + selfLoop;
		if (isLiteralOrUri)
			st += "literalOrUriCode: " + literalOrUriCode;
		if (satellites_in.size() > 0) {
			MutableIntIterator its = satellites_in.keySet().intIterator();
			while (its.hasNext()) {
				int val = its.next();
				st += "\t\t IN " + val + " " + satellites_in.get(val) + "\n";
			}
		}
		if (satellites_out.size() > 0) {
			MutableIntIterator its = satellites_out.keySet().intIterator();
			while (its.hasNext()) {
				int val = its.next();
				st += "\t\t OUT " + val + " " + satellites_out.get(val) + "\n";
			}
		}

		return st;
	}

}
