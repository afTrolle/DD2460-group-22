/* $Id: DaytimeServer.java 838 2010-11-24 08:16:23Z cartho $ */

/* Daytime server (implementing RFC 867).
 * This modified version aborts after having served one client. */

import java.io.IOException;
import env.java.io.OutputStreamWriter;
import env.java.net.ServerSocket;
import env.java.net.Socket;
import env.java.util.Date;

public class DaytimeServer {

  public final static int PORT = 1024;  //13;

  public static void main(String[]args) {
    Socket connection = null;
    ServerSocket server = null;
    try {
      server = new ServerSocket(PORT);

      while (true) {
        connection = server.accept();
        OutputStreamWriter out
          = new OutputStreamWriter(connection.getOutputStream());
        Date now = new Date();
        out.write(now.toString() + "\n");
        out.flush();
      }
    }
    catch(Exception e) {
      System.err.println(e);
    }
    finally {
      try {
		  if (connection != null){
				connection.close();
		  }
		  if (server != null) {
			server.close();
		}
      }
      catch(IOException e) {
        System.err.println(e);
      }
      System.out.println("Connection closed.");
    }
  }
}
