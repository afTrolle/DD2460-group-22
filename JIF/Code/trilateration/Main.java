package trilateration;

import java.util.Random;

import project.DatingApp01;
import project.NodeAlice;

public class Main {

	public static void main(String[] args) {
		
		//Init Dating Application
		DatingApp01 app = new DatingApp01();
		//Set bob on some random coordinates
		Random r = new Random();
		int rangeMax = 100;
		int rangeMin = -100;
		int highDistance = Integer.MAX_VALUE;
		
		//generate bob and chuck  coordinates
		double bobX = rangeMin + (rangeMax - rangeMin) * r.nextDouble();
		double bobY = rangeMin + (rangeMax - rangeMin) * r.nextDouble();
		
		double chuckX = rangeMin + (rangeMax - rangeMin) * r.nextDouble();
		double chuckY = rangeMin + (rangeMax - rangeMin) * r.nextDouble();
		
		//update/set Bob and Chuck coordinates
		app.updateBob(bobX, bobY, "BobPhone", highDistance);
		app.updateChuck(chuckX, chuckY, "ChuckPhone", highDistance);
		
		//Print Bobs coordinates for debuging
		System.out.println("Bobs coordinates:" + "X:"+bobX+ "  Y:"+bobY);
		
		System.out.println("Chucks coordinates:"+ "X:"+chuckX+ "  Y:"+chuckY);
		System.out.println();	
		
		// use trilateration
		TrilaterationAppExploit appExploit = new TrilaterationAppExploit(app);
		
		System.out.println("Trilateration Guesses for Bob { X:"+ appExploit.getBobX() +  " Y:"+appExploit.getBobY()+ "}");
		System.out.println("Trilateration Guesses for Chuck { X:"+ appExploit.getChuckX() +  " Y:"+appExploit.getChuckY()+ "}");
	}
	



}
