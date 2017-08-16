package query;

import java.util.Comparator;

/**
 * A link between two {@link ObjectPath}, the nodes of the query's spanning
 * tree. They are 2 types of links : {@link NormalLinkPath}, which represent
 * link with a single predicate, and {@link PPLinkPath}, property paths links.
 * 
 * @author brett
 *
 */
public abstract class LinkObjectPath implements Comparator<LinkObjectPath>, Comparable<LinkObjectPath> {
	public int previous_id;
	public int rank_previous_id;
	public int direction;
	/**
	 * if equals to 0, this link is a {@link NormalLinkPath}, otherwise it's a
	 * {@link PPLinkPath}.
	 */
	public int linkType;

	public LinkObjectPath(int previous_id, int rank_previous_id, int direction) {
		this.previous_id = previous_id;
		this.rank_previous_id = rank_previous_id;
		this.direction = direction;
	}

	public abstract int size();

	public abstract String toString();

	@Override
	public int compare(LinkObjectPath d, LinkObjectPath d1) {
		if (d.size() > d1.size())
			return -1;
		else if (d.size() == d1.size())
			return 0;
		else
			return 1;
	}

	@Override
	public int compareTo(LinkObjectPath d) {
		if (size() > d.size())
			return -1;
		else if (size() == d.size())
			return 0;
		else
			return 1;
	}

}
