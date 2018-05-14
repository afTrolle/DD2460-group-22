package env.java.net;
import java.io.IOException;
import env.java.io.InputStream;
import env.java.io.OutputStream;

public class Socket {
    InputStream istr;
    OutputStream ostr;

    public Socket() {
	istr = new InputStream();
	ostr = new OutputStream(istr);
    }

    public Socket(String host, int port) throws IOException {
	this();
	connect();
    }

    /** Allow a client to connect to a port. */
    public void connect() throws IOException {
    }

    public void close() throws IOException {
    }

    public OutputStream getOutputStream() throws IOException {
	return ostr;
    }

    public InputStream getInputStream() throws IOException {
	return istr;
    }
}
