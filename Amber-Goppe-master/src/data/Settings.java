/*
 * 
 * Class that contains all the constant employed by the Amber framework
 * 
 * 
 * */


package data;

public class Settings {
	public static int INIT_SIZE = 1000000;
	public static int ARRAY_SIZE = 64000;
	public static float load_factor = 0.95f;
	public static byte N_FEAT = 4;
	public static byte SYNOPSIS_SIZE = (byte) (N_FEAT * 2);
	public static String TEMP_EXTENSION = ".temp";
	public static int OUT = -1;
	public static int IN = 1;
	public static int VARIABLE = -1;
}
