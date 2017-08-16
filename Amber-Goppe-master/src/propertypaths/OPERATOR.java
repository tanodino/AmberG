package propertypaths;

public enum OPERATOR {
	ALT('|'), SEQ('/'), INV('^'), ZeroOrMore('*'), OneOrMore('+'), ZeroOrOne('?'), Link('$'), NEG('!');

	public char asChar() {
		return asChar;
	}

	private final char asChar;

	private OPERATOR(char asChar) {
		this.asChar = asChar;
	}

	public static boolean isBinary(OPERATOR o) {
		Character c = o.asChar;
		boolean toReturn = false;
		if (c == '|' || c == '/')
			toReturn = true;
		return toReturn;
	}
}