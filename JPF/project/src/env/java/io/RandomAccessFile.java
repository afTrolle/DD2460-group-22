package env.java.io;

import java.io.*;

/*  class of RandomAccessFile; multiple instances access
   the <em>same</em> file. */
public class RandomAccessFile {
	final static int MAX_SIZE = 8;
	private boolean canWrite = false;
	private boolean isClosed = false;
	private static int size = 0;
	private int pos = 0;
	private static byte[] data = new byte[MAX_SIZE];

	public RandomAccessFile(File file, String mode) throws FileNotFoundException {
		// ignore file name to keep the model as simple as possible
		if (mode.indexOf('w') != -1) {
			canWrite = true;
		}
	}

	public void close() throws IOException {
		isClosed = true;
	}

	public int length() throws IOException {
		if (isClosed) throw new IOException ("File is closed");
		return size;
	}

	public int read(byte[] b, int off, int len) throws IOException {
		if (isClosed) throw new IOException ("File is closed");
		if (pos == size) {
			return -1;
		}
		int read = 0;
		while (off < len && pos < size) {
			b[off++] = data[pos++];
			read++;
		}
		return read;
	}

	public void seek(long pos) throws IOException {
		if (isClosed) throw new IOException ("File is closed");
		if (pos < 0) throw new IOException("Position < 0");
		this.pos = (int)pos;
	}

	public void write(byte[]b, int off, int len) throws IOException {
		if (!canWrite) throw new IOException("Write called on read-only file");
		if (isClosed) throw new IOException ("File is closed");
		while (off < len && pos < MAX_SIZE) {
			data[pos++] = b[off++];
			if (pos >= size)
				size = pos;
		}
		if (pos == MAX_SIZE && off < len) {
			throw new IOException("Simulated disk full");
		}
	}
}
