//
// Copyright (C) 2006 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

/* An example of a very simple, multi-threaded HTTP server.
 * Implementation notes are in WebServer.html, and also
 * as comments in the source code. */

import java.io.*;
import java.net.*;
import java.util.*;

class WebServer implements HttpConstants {

	/* static class data/methods */

	/* print to stdout */
	protected static void p(String s) {
		System.out.println(s);
	}

	/* print to the log file */
	protected static void log(String s) {
		synchronized (log) {
			log.println(s);
			log.flush();
		}
	}

	static PrintStream log = null;
	/*
	 * our server's configuration information is stored in these properties
	 */
	protected static Properties props = new Properties();

	/* Where worker threads stand idle */
	static Vector threads = new Vector();

	/* the web server's virtual root */
	static File root;

	/* timeout on client connections */
	static int timeout = 0;

	/* max # worker threads */
	static int workers = 0;

	static int seq_len = 3;

	/* load www-server.properties from java.home */
	static void loadProps() throws IOException {
		File f = new File(System.getProperty("java.home") + File.separator + "lib" + File.separator + "www-server.properties");
		if (f.exists()) {
			InputStream is = new BufferedInputStream(new FileInputStream(f));
			props.load(is);
			is.close();
			String r = props.getProperty("root");
			if (r != null) {
				root = new File(r);
				if (!root.exists()) {
					throw new Error(root + " doesn't exist as server root");
				}
			}
			r = props.getProperty("timeout");
			if (r != null) {
				timeout = Integer.parseInt(r);
			}
			r = props.getProperty("workers");
			if (r != null) {
				workers = Integer.parseInt(r);
			}
			r = props.getProperty("log");
			if (r != null) {
				p("opening log file: " + r);
				log = new PrintStream(new BufferedOutputStream(new FileOutputStream(r)));
			}
		}

		/* if no properties were specified, choose defaults */
		if (root == null) {
			root = new File(System.getProperty("user.dir"));
		}
		if (timeout <= 1000) {
			timeout = 5000;
		}
/*		if (workers < 25) {
			workers = 5;
		}*/
		if (log == null) {
			p("logging to stdout");
			log = System.out;
		}
	}

	static void printProps() {
		p("root=" + root);
		p("timeout=" + timeout);
		p("workers=" + workers);
	}

	public static void main(String[] a) throws Exception {
		int port = 8080;
		int n = 2; // number of requests

		if (a.length > 1) {
			port = Integer.parseInt(a[0]);
			seq_len = Integer.parseInt(a[1]);
		}

		loadProps();
		printProps();
		/* start worker threads */
		for (int i = 0; i < workers; ++i) {
			Worker w = new Worker();
			(new Thread(w, "worker #" + i)).start();
			threads.addElement(w);
		}

		ServerSocket ss = new ServerSocket(port);
		while (--n >= 0) {

			Socket s = ss.accept();

			Worker w = null;
//			synchronized (threads) {
//				if (threads.isEmpty()) {
					Worker ws = new Worker();
					ws.setSocket(s);
//					(new Thread(ws, "additional worker")).start();
					ws.handleClient(); // execute in main thread
//				} else {
//					w = (Worker) threads.elementAt(0);
//					threads.removeElementAt(0);
//					w.setSocket(s);
//				}
//			}
		}
	}
}

class Worker extends WebServer implements HttpConstants, Runnable {
	final static int BUF_SIZE = 5;// 2048;

	//static final byte[] EOL = { (byte) '\r', (byte) '\n' };
	static final char EOL = '\n';

	/* buffer to use for requests */
	byte[] buf;
	/* Socket to client we're handling */
	private Socket s;

	Worker() {
		buf = new byte[BUF_SIZE];
		s = null;
	}

	synchronized void setSocket(Socket s) {
		this.s = s;
		notify();
	}

	public synchronized void run() {
		while (true) {
			if (s == null) {
				/* nothing to do */
				try {
					wait();
				} catch (InterruptedException e) {
					/* should not happen */
					continue;
				}
			}
			try {
				handleClient();
			} catch (Exception e) {
				e.printStackTrace();
			}
			/*
			 * go back in wait queue if there's fewer than numHandler connections.
			 */
			s = null;
//			Vector pool = WebServer.threads;
//			synchronized (pool) {
//				if (pool.size() >= WebServer.workers) {
					/* too many threads, exit this one */
					return;
//				} else {
//					pool.addElement(this);
//				}
//			}
		}
	}

	void handleClient() throws IOException {
		InputStream is = new BufferedInputStream(s.getInputStream());
		BufferedReader reader = new BufferedReader(new InputStreamReader(is));
		PrintStream ps = new PrintStream(s.getOutputStream());
		/*
		 * we will only block in read for this many milliseconds before we fail with java.io.InterruptedIOException, at which point we will
		 * abandon the connection.
		 */
		// s.setSoTimeout(WebServer.timeout);
		// s.setTcpNoDelay(true);
		try {
			/*
			 * We only support HTTP GET/HEAD, and don't support any fancy HTTP options, so we're only interested really in the first line.
			 */
//			int nread = 0, r = 0;
//			/* zero out the buffer from last time */
//			for (int i = 0; i < BUF_SIZE; i++) {
//				buf[i] = 0;
//			}
//
			String line = reader.readLine();
//			
//			if(line == null) {
//				System.out.println("Null request");
//				return;
//			}
//
//			/* are we doing a GET or just a HEAD */
			boolean doingGet = true;
//			/* beginning of file name */
//			int index;
//			if (line.startsWith("GET ")) {
//				doingGet = true;
//				index = 4;
//			} else if (line.startsWith("HEAD ")) {
//				doingGet = false;
//				index = 5;
//			} else {
//				/* we don't support this method */
//				ps.println("HTTP/1.1 " + HTTP_BAD_METHOD + " unsupported method type in request " + line);
//				ps.flush();
//				s.close();
//				return;
//			}
//
//			int i = 0;
			/*
			 * find the file name, from: GET /foo/bar.html HTTP/1.1 extract "/foo/bar.html"
			 */
//			line = line.substring(index);
//			index = line.indexOf(' ');
			String fname = null;
//			if (index > -1)
//				fname = (line.substring(0, index)).replace('/', File.separatorChar);
//			else
//				fname = line;
//			if (fname.startsWith(File.separator)) {
//				fname = fname.substring(1);
//			}
//
			int start = 0;
			int end = Integer.MAX_VALUE;
//			while (!(line = reader.readLine()).equals("")) {
				// System.err.println(line);
				if (line.startsWith("Range: bytes")) {
					int eq = line.indexOf('=');
					int idx = line.indexOf('-');
					String rangeStart = line.substring(eq + 1, idx);
					String rangeEnd = line.substring(idx + 1);
					start = Integer.parseInt(rangeStart);
					end = Integer.parseInt(rangeEnd);
					// System.out.println("Range: " + start + " - " + end);
				}
//			}

			boolean OK = printHeaders(fname, ps);
			if (doingGet) {
				if (OK) {
					sendFile(fname, ps, start, end);
				} else {
					send404(ps);
				}
			}
		} finally {
//			s.close();
			// do not close socket because jpf-nas does not work properly in that case
		}
	}

	boolean printHeaders(String name, PrintStream ps) throws IOException {
		// boolean ret = false;
		int rCode = 0;

		rCode = HTTP_OK;
		// ret = true;

		log(/*"From " + s.getInetAddress().getHostAddress() + ":*/ "GET " + name + "-->" + rCode);
		// ps.print("Server: Simple java");
		// ps.write(EOL);
		// ps.print("Date: " + (new Date()));
		// ps.write(EOL);
		ps.println("HTTP/1.1 " + HTTP_OK + " OK" + EOL +
			   "Content-Length: " + WebServer.seq_len + EOL +
			   "Accept-Ranges: bytes");
		ps.flush();
		// ps.print("Last Modified: " + (new
		// Date(targ.lastModified())));
		// ps.write(EOL);
/*
		int ind = name.lastIndexOf('.');
		String ct = null;
		if (ind > 0) {
			ct = (String) map.get(name.substring(ind));
		}
		if (ct == null) {
			ct = "unknown/unknown";
		}
*/
		// ps.print("Content-type: " + ct);
		// ps.write(EOL);
		return true;
	}

	void send404(PrintStream ps) throws IOException {
		ps.write(EOL);
		ps.write(EOL);
		ps.println("Not Found\n\n" + "The requested resource was not found.\n");
	}

	void sendFile(String name, PrintStream ps, int start, int end) throws IOException {
		//ps.write(EOL);
		ps.println();

		if (end >= seq_len)
			end = (int) (seq_len - 1);

		if (start < 0)
			start = 0;

		int n;
		boolean noLimit = end == Integer.MAX_VALUE;
		int len = end - start + 1;

		// Fill buffer with a sequence of alphabets
		for (int i = 0; i < seq_len; i++)
			buf[i] = (byte) ('a' + (start + i));

		ps.write(buf, start, len);
	}

	/* mapping of file extensions to content-types */
	/* static java.util.Hashtable map = new java.util.Hashtable();

	static {
		fillMap();
	}

	static void setSuffix(String k, String v) {
		map.put(k, v);
	}

	static void fillMap() {
		setSuffix("", "content/unknown");
		setSuffix(".uu", "application/octet-stream");
		setSuffix(".exe", "application/octet-stream");
		setSuffix(".ps", "application/postscript");
		setSuffix(".zip", "application/zip");
		setSuffix(".sh", "application/x-shar");
		setSuffix(".tar", "application/x-tar");
		setSuffix(".snd", "audio/basic");
		setSuffix(".au", "audio/basic");
		setSuffix(".wav", "audio/x-wav");
		setSuffix(".gif", "image/gif");
		setSuffix(".jpg", "image/jpeg");
		setSuffix(".jpeg", "image/jpeg");
		setSuffix(".htm", "text/html");
		setSuffix(".html", "text/html");
		setSuffix(".text", "text/plain");
		setSuffix(".c", "text/plain");
		setSuffix(".cc", "text/plain");
		setSuffix(".c++", "text/plain");
		setSuffix(".h", "text/plain");
		setSuffix(".pl", "text/plain");
		setSuffix(".txt", "text/plain");
		setSuffix(".java", "text/plain");
	}

	void listDirectory(File dir, PrintStream ps) throws IOException {
		ps.println("<TITLE>Directory listing</TITLE><P>\n");
		ps.println("<A HREF=\"..\">Parent Directory</A><BR>\n");
		String[] list = dir.list();
		for (int i = 0; list != null && i < list.length; i++) {
			File f = new File(dir, list[i]);
			if (f.isDirectory()) {
				ps.println("<A HREF=\"" + list[i] + "/\">" + list[i] + "/</A><BR>");
			} else {
				ps.println("<A HREF=\"" + list[i] + "\">" + list[i] + "</A><BR");
			}
		}
		ps.println("<P><HR><BR><I>" + (new Date()) + "</I>");
	}*/

}

interface HttpConstants {
	/** 2XX: generally "OK" */
	public static final int HTTP_OK = 200;
	public static final int HTTP_CREATED = 201;
	public static final int HTTP_ACCEPTED = 202;
	public static final int HTTP_NOT_AUTHORITATIVE = 203;
	public static final int HTTP_NO_CONTENT = 204;
	public static final int HTTP_RESET = 205;
	public static final int HTTP_PARTIAL = 206;

	/** 3XX: relocation/redirect */
	public static final int HTTP_MULT_CHOICE = 300;
	public static final int HTTP_MOVED_PERM = 301;
	public static final int HTTP_MOVED_TEMP = 302;
	public static final int HTTP_SEE_OTHER = 303;
	public static final int HTTP_NOT_MODIFIED = 304;
	public static final int HTTP_USE_PROXY = 305;

	/** 4XX: client error */
	public static final int HTTP_BAD_REQUEST = 400;
	public static final int HTTP_UNAUTHORIZED = 401;
	public static final int HTTP_PAYMENT_REQUIRED = 402;
	public static final int HTTP_FORBIDDEN = 403;
	public static final int HTTP_NOT_FOUND = 404;
	public static final int HTTP_BAD_METHOD = 405;
	public static final int HTTP_NOT_ACCEPTABLE = 406;
	public static final int HTTP_PROXY_AUTH = 407;
	public static final int HTTP_CLIENT_TIMEOUT = 408;
	public static final int HTTP_CONFLICT = 409;
	public static final int HTTP_GONE = 410;
	public static final int HTTP_LENGTH_REQUIRED = 411;
	public static final int HTTP_PRECON_FAILED = 412;
	public static final int HTTP_ENTITY_TOO_LARGE = 413;
	public static final int HTTP_REQ_TOO_LONG = 414;
	public static final int HTTP_UNSUPPORTED_TYPE = 415;

	/** 5XX: server error */
	public static final int HTTP_SERVER_ERROR = 500;
	public static final int HTTP_INTERNAL_ERROR = 501;
	public static final int HTTP_BAD_GATEWAY = 502;
	public static final int HTTP_UNAVAILABLE = 503;
	public static final int HTTP_GATEWAY_TIMEOUT = 504;
	public static final int HTTP_VERSION = 505;
}
