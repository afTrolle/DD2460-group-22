package env.java.io;

public class PrintWriter {

  private OutputStream out;

  public PrintWriter(OutputStream out, boolean autoflush) {
    this.out = out;
  }

  public void println(String line) {
	assert (line.startsWith("Range: bytes"));
	int eq = line.indexOf('=');
	int idx = line.indexOf('-');
	String rangeStart = line.substring(eq + 1, idx);
	//String rangeEnd = line.substring(idx + 1);
	int start = Integer.parseInt(rangeStart);
	//end = Integer.parseInt(rangeEnd);
	out.in.start = start;
	// set correct start position for data being returned
  }

  public void close() {
  }
}
