package env.java.io;

public class InputStream {
	static final int HTTP_OK = 200;
	static final char EOL = '\n';
	static final int CONTENT_LENGTH = 3;

	final static String HEADER =
		"HTTP/1.1 " + HTTP_OK + " OK" + EOL +
		"Content-Length: " + CONTENT_LENGTH + EOL +
		"Accept-Ranges: bytes" + EOL;
	int pos; // denotes position in header
	int start; // position in data

	public InputStream() {
	}

	public void close() {
	}

	/** TODO: Implement the read operation for the HTTP payload.
	  * This means the same data has to be returned as in sendFile in
	  * the web server. */
	public int read(byte[] b, int off, int len) {
		int read = 0;
		return read;
	}

	/** TODO: Implement the read operation for the HTTP header.
	  * This means that the next character in HEADER has to be
	  * returned, or -1 if the end has been reached. */
	public int read() {
		return -1;
	}
}
