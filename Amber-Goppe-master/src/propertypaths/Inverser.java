package propertypaths;

import java.util.ArrayList;

public class Inverser {
	private ArrayList<String> regex;

	public Inverser(String regex) {
		cutRegex(regex);
		// System.out.println(this.regex);
	}

	public String getInversed() {
		// System.out.println("INVERSING : "+regex);
		ArrayList<String> inversed = this.computeInverse(regex);
		String inverse = new String();
		for (String s : inversed)
			inverse += s;
		return inverse;
	}

	private ArrayList<String> inverse(ArrayList<String> buffer) {
		// System.out.println(">> INVERSING "+buffer);
		ArrayList<String> result = new ArrayList<>();
		for (int i = buffer.size() - 1; i >= 0; i--) {
			if (buffer.get(i).startsWith("<"))
				result.add("^" + buffer.get(i));
			else {
				if (buffer.get(i).equals("("))
					result.add(")");
				else if (buffer.get(i).equals(")"))
					result.add("(");
				else if (buffer.get(i).startsWith("^<")) {
					result.add(buffer.get(i).substring(1));
				} else
					result.add(buffer.get(i));
			}
		}
		// System.out.println(result);
		ArrayList<String> temp = new ArrayList<>(result);
		for (int i = 0; i < temp.size(); i++) {
			if (temp.get(i).matches("^[\\.\\?\\+\\*]$")) {
				int j = i;
				int count_parenthesis = 0;
				do {
					j++;
					if (temp.get(j).equals(")"))
						count_parenthesis--;
					if (temp.get(j).equals("("))
						count_parenthesis++;
				} while (count_parenthesis > 0);
				// while (!temp.get(j).equals(")"))
				// j += 1;
				result.add(j + 1, result.get(i));
				result.remove(i);
			}
		}
		return result;
	}

	private ArrayList<String> computeInverse(ArrayList<String> current) {
		ArrayList<String> result = new ArrayList<>();
		for (int i = 0; i < current.size(); i++) {
			if (current.get(i).equals("^") && current.get(i + 1).equals("(")) {
				ArrayList<String> buffer = new ArrayList<>();
				int count_parenthesis = 0;
				do {
					i++;
					if (current.get(i).equals("(")) {
						count_parenthesis++;
						buffer.add("(");

					} else if (current.get(i).equals(")")) {
						count_parenthesis--;
						buffer.add(")");
					} else
						buffer.add(current.get(i));
				} while (count_parenthesis > 0);
				if (buffer.contains("^")) {
					result.addAll(inverse(computeInverse(buffer)));
				} else {
					result.addAll(inverse(buffer));
				}
			} else {
				result.add(current.get(i));
			}

		}

		return result;
	}

	private void cutRegex(String regex) {
		ArrayList<String> result = new ArrayList<>();
		for (int i = 0; i < regex.length(); i++) {
			if (regex.charAt(i) == '<' || (regex.charAt(i) == '^' && regex.charAt(i + 1) == '<')) {
				String buffer = "" + regex.charAt(i);
				do {
					i++;
					buffer += regex.charAt(i);
				} while (regex.charAt(i) != '>');
				if (i + 1 < regex.length()
						&& (regex.charAt(i + 1) == '*' || regex.charAt(i + 1) == '+' || regex.charAt(i + 1) == '?')) {
					buffer += regex.charAt(i + 1);
					i++;
				}
				result.add(buffer);
			} else {
				result.add(new String() + regex.charAt(i));
			}
		}
		this.regex = result;
	}
}