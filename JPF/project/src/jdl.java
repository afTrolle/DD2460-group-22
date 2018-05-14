public class jdl {
	static public void main(String[] args) throws Exception {
		Downloader dl = Downloader.getMain();
		dl.configure(/*args[0]*/"http://" + java.net.InetAddress.getLocalHost().getHostName() + "/test");
		dl.download();
	}
}
