package propertypaths;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import data.GoppeGraphDatabase;

public class PPSolver {

	private String pp = "";
	private String regex = "";

	@SuppressWarnings("unused")
	private PPSolver() {
	}

	/**
	 * Prend un property path et le transforme en expression régulière. Chaque
	 * IRI du PP est associée à un caractère, et inversement. Remplace également
	 * les '/' par ''.
	 */
	public PPSolver(String pp) {
		this.pp = pp;
		pp = pp.replace(" ", "");
		final String regex = "(\\^?)<(([^:\\/?#]+:)?(\\/\\/[^\\/?#]*?)?[^?#]*?(\\\\?[^#]*?)?(#.*?)?)>";
		Pattern p = Pattern.compile(regex);
		Matcher matcher = p.matcher(pp);
		while (matcher.find()) {
			String fullMatch = matcher.group(0);
			String iri = matcher.group(2);
			int iriCode = GoppeGraphDatabase.getDatabase().convertStringToIntP("<" + iri + ">");
			Character iriToChar;
			if (matcher.group(1).equals("^")) {
				iriToChar = (char) (iriCode + GoppeGraphDatabase.getDatabase().getCharacterShift());
				fullMatch = "\\" + fullMatch;
			} else {
				iriToChar = (char) iriCode;
			}
			pp = pp.replaceFirst(fullMatch, iriToChar.toString());
		}
		// System.out.println("POST REPLACING SIMPLE : " + pp);

		final String rNeg = "(\\!\\(.*?\\))|\\!.";
		p = Pattern.compile(rNeg);
		matcher = p.matcher(pp);
		int i = 2 * GoppeGraphDatabase.getDatabase().getCharacterShift();
		while (matcher.find()) {
			String m = matcher.group(0);
			// System.out.println("full match : " + m);
			GoppeGraphDatabase.getDatabase().addNegationSet(m, i);
			// System.out.println("forbidden for " + (char) i + " = " +
			// GoppeGraphDatabase.getDatabase().getNegationSet(i));
			pp = pp.replace(m, "" + (char) i);
			i += 1;
		}

		this.regex = pp.replace("/", "");
		// System.out.println("regex : " + this.regex);
	}

	public String getPp() {
		return pp;
	}

	public String getRegex() {
		return regex;
	}
}
