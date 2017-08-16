package org.khelekore.prtree;

public class NDMBRConverter implements MBRConverter<SimplePointND>{
	private int dim;
	
	public NDMBRConverter(int dim){
		this.dim = dim;
	}
	
	@Override
	public int getDimensions() {
		return this.dim;
	}

	@Override
	public short getMin(int axis, SimplePointND t) {
		return t.getOrd(axis);
	}

	@Override
	public short getMax(int axis, SimplePointND t) {
		return t.getOrd(axis);
	}

}
