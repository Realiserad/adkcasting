import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Random;
import java.util.StringTokenizer;

/**
 * Casting.java implements heuristics for solving the casting problem.
 * Problem description is available here: http://www.csc.kth.se/utbildning/kth/kurser/DD1352/adk12/labb4/
 * Best Kattis submission is available here: https://kth.kattis.com/submissions/689486 (446 points)
 * 
 * @author Bastian Fredriksson (bastianf@kth.se)
 */
public class Casting {
	private class Kattio extends PrintWriter {
		private BufferedReader r;
		private String line;
		private StringTokenizer st;
		private String token;

		public Kattio(InputStream i, OutputStream o) {
			super(new BufferedOutputStream(o));
			r = new BufferedReader(new InputStreamReader(i));
		}

		public int getInt() {
			return Integer.parseInt(nextToken());
		}

		private String peekToken() {
			if (token == null) 
				try {
					while (st == null || !st.hasMoreTokens()) {
						line = r.readLine();
						if (line == null) return null;
						st = new StringTokenizer(line);
					}
					token = st.nextToken();
				} catch (IOException e) { }
			return token;
		}

		private String nextToken() {
			String ans = peekToken();
			token = null;
			return ans;
		}
	}

	private final int SUPER_ACTOR = -1;
	private ArrayList<HashSet<Integer>> roleToActorSet;// X.get(i-1) contains the actors who can play role i
	private ArrayList<Integer[]> roleToActorArray;
	private ArrayList<HashSet<Integer>> sceneToRoleSet;// X.get(i) contains the roles who play in scene i
	private ArrayList<Integer[]> sceneToRoleArray;
	private int[] casting; 							// casting[i-1] contains the actor who will play role i
	private int[] divaRoles = new int[3];         	// divaRoles[i] contains the immutable role for diva i
	private LinkedList<Integer> diva1Roles = new LinkedList<Integer>();
	private LinkedList<Integer> diva2Roles = new LinkedList<Integer>();
	private int NUM_ROLES, NUM_SCENES, NUM_ACTORS;
	int[] roleCount;                                 	// roleCount[i-1] contains the number of roles actor i can play
	private ArrayList<ArrayList<Integer>> roleToScenes;	// roleToScenes.get(i-1) contains all scenes role i belongs to
	private ArrayList<HashSet<Integer>> actorsInScene;	// actorsInScene.get(i) contains the actors currently playing in scene i
	private Random random = new Random();
	private int[] production;                       	// production[i-1] contains the number of actor i:s playing

	public static void main(String[] args) {
		new Casting();
	}

	public Casting() {
		Kattio io = new Kattio(System.in, System.out);

		NUM_ROLES = io.getInt();
		NUM_SCENES = io.getInt();
		NUM_ACTORS = io.getInt();

		roleToActorSet = new ArrayList<HashSet<Integer>>(NUM_ROLES);
		sceneToRoleSet = new ArrayList<HashSet<Integer>>(NUM_SCENES);
		roleToActorArray = new ArrayList<Integer[]>(NUM_ROLES);
		sceneToRoleArray = new ArrayList<Integer[]>(NUM_SCENES);
		casting = new int[NUM_ROLES];
		roleCount = new int[NUM_ACTORS];
		roleToScenes = new ArrayList<ArrayList<Integer>>(NUM_ROLES);
		actorsInScene = new ArrayList<HashSet<Integer>>(NUM_SCENES);
		production = new int[NUM_ACTORS]; 

		for (int i = 0; i < NUM_ROLES; i++) roleToScenes.add(new ArrayList<Integer>());
		for (int i = 0; i < NUM_SCENES; i++) actorsInScene.add(new HashSet<Integer>());

		/*-----------------------------------------------------------------------*/
		/*-----------------------------------------------------------------------*/
		/*                            READ INPUT                                 */

		// Read roles
		for (int i = 0; i < NUM_ROLES; i++) {
			final int ROW_SIZE = io.getInt();
			HashSet<Integer> set = new HashSet<Integer>((int)(ROW_SIZE / 0.75 + 1));
			Integer[] array = new Integer[ROW_SIZE];

			for (int j = 0; j < ROW_SIZE; j++) {
				int actor = io.getInt();

				if (actor == 1) diva1Roles.add(i+1); // Role i+1 can be played by diva 1
				else if (actor == 2) diva2Roles.add(i+1);
				roleCount[actor-1]++;
				set.add(actor);
				array[j] = actor;
			}

			roleToActorSet.add(set);
			roleToActorArray.add(array);
		}

		// Read scenes
		for (int i = 0; i < NUM_SCENES; i++) { 
			final int ROW_SIZE = io.getInt();
			HashSet<Integer> set = new HashSet<Integer>((int)(ROW_SIZE / 0.75 + 1));
			Integer[] array = new Integer[ROW_SIZE];

			for (int j = 0; j < ROW_SIZE; j++) {
				int role = io.getInt();

				roleToScenes.get(role-1).add(i);
				set.add(role);
				array[j] = role;
			}

			sceneToRoleSet.add(set);
			sceneToRoleArray.add(array);
		}

		/*-----------------------------------------------------------------------*/
		/*-----------------------------------------------------------------------*/
		/*                              HEURESTICS                               */

		/* My overall strategy is as follows: Begin by assigning one role each to the two 
		 * divas. Process each role in order, and try to find an actor who can play this 
		 * role without violating any constraints. Prioritize actors who can play many roles 
		 * since this will increase the changes of reuse. If no actor can be found, use 
		 * a super actor and be happy. */

		for (Integer[] actors : roleToActorArray) {
			Collections.sort(Arrays.asList(actors), new Comparator<Integer>() {
				@Override
				public int compare(Integer a, Integer b) {
					return roleCount[b-1] - roleCount[a-1];
				}
			});
		}

		assignDivas(); // the roles chosen for the divas will be put in divaRoles[]

		for (int i = 0; i < casting.length; i++) {
			int role = i+1;

			if (role == divaRoles[1] || role == divaRoles[2]) continue;

			boolean success = false;
			Integer[] actors = roleToActorArray.get(i);
			for (int j = 0; j < actors.length; j++) {
				if (tryAssign(role, actors[j])) {
					assign(role, actors[j]);
					success = true;
					break;
				}
			}

			if (!success) markWithSuperActor(role);
		}

		/* This will give us a B with good margin, but we want more. Muhahah */
		for (int i = 0; i < NUM_ROLES * 7; i++) loc2search();

		/*-----------------------------------------------------------------------*/
		/*-----------------------------------------------------------------------*/
		/*                           PRINT RESULT                                */

		int buckets = employSuperActors();

		// entries -> {
		//   [actor1] --> role1 ~> role2 ~> null
		//   [actor2] --> null
		//   [actor3] --> role3 ~> role4 ~> role5 ~> null
		//   [actor4] --> role6 ~> null
		// }
		ArrayList<LinkedList<Integer>> entries = new ArrayList<LinkedList<Integer>>(buckets);
		for (int i = 0; i < buckets; i++) entries.add(new LinkedList<Integer>());

		// Fill the entries with roles
		for (int i = 0; i < casting.length; i++) {
			entries.get(casting[i]-1).add(i+1);
		}

		// Count the number of actors with at least one role
		int actorsUsed = 0;
		for (int i = 0; i < entries.size(); i++) {
			if (!entries.get(i).isEmpty()) {
				actorsUsed++;
			}
		}

		StringBuilder sb = new StringBuilder();
		sb.append(actorsUsed + "\n");

		for (int i = 0; i < entries.size(); i++) {
			LinkedList<Integer> entry = entries.get(i);
			if (!entry.isEmpty()) {
				sb.append(i+1 + " " + entry.size());
				for (Integer role : entry) {
					sb.append(" " + role);
				}
				sb.append("\n");
			}
		}

		io.print(sb.toString());
		io.close();
	}

	/**
	 * Returns true if the role given as argument is played by a super actor.
	 */
	private boolean superActor(int role) {
		if (getActor(role) == SUPER_ACTOR) return true;
		return false;
	}

	/**
	 * Retrieve the actor currently playing the role given as argument.
	 * @return The actor for the role specified or zero if no actor is casting
	 */
	private int getActor(int role) {
		return casting[role-1];
	}

	private int employSuperActors() {
		int nextSuperActor = NUM_ACTORS;
		for (int i = 0; i < casting.length; i++) {
			if (casting[i] == SUPER_ACTOR) {
				nextSuperActor++;
				casting[i] = nextSuperActor;
			}
		}
		return nextSuperActor; // return upper limit on number of actors
	}


	/**
	 * Assign roles to the two divas. This method ensures that the divas never
	 * play in the same scene. However, it might put a diva in a scene already containing
	 * a diva, so this method should be invoked before making any assigments.
	 * The method picks the first pair of roles available, by traversing the lists
	 * diva1Roles and diva2Roles from left to right.
	 */
	private void assignDivas() {
		for (Integer diva1Role : diva1Roles) {
			for (Integer diva2Role : diva2Roles) {
				if (!diva1Role.equals(diva2Role) && !inSameScene(diva1Role, diva2Role)) {
					assign(diva1Role, 1);
					assign(diva2Role, 2);
					divaRoles[1] = diva1Role;
					divaRoles[2] = diva2Role;
					return;
				}
			}
		}
	}

	/**
	 * Check whether two roles ever play in the same scene.
	 * @return True if the roles play in at least one scene together
	 */
	private boolean inSameScene(int r1, int r2) {
		for (HashSet<Integer> scene : sceneToRoleSet) {
			if (scene.contains(r1) && scene.contains(r2)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns true if the role given as argument is played by a diva.
	 */
	private boolean hasDiva(int role) {
		return (casting[role-1] == 1 || casting[role-1] == 2) ? true : false;
	}

	/**
	 * Try to assign the actor given as first argument, the role given as second
	 * argument. The method will only return true if the assigment does not violate 
	 * any of the two constraints below:
	 * 1. Two divas are not allowed to play in the same scene
	 * 2. An actor is not allowed to play two roles in a scene
	 * @return True if an assigment can be made, false otherwise
	 */
	private boolean tryAssign(int role, int actor) {
		ArrayList<Integer> scenes = roleToScenes.get(role-1);
		for (int scene : scenes) {
			HashSet<Integer> actors = actorsInScene.get(scene);
			/* Check contraint 1. Ensure the other diva is not already present */
			if (actor == 1 && actors.contains(2)) return false;
			if (actor == 2 && actors.contains(1)) return false;
			/* Check constraint 2. Ensure the actor given as input is not already
			 * present (duplicate). */
			if (actors.contains(actor)) return false;
		}
		/* The assigment can be performed safely */
		return true;
	}

	/**
	 * Let the role given as first argument be played by the actor given
	 * as second argument. You should invoke tryAssign() first, to make
	 * sure that the assigment is valid.
	 */
	private void assign(int role, int actor) {
		if (hasActor(role)) unassign(role);
		casting[role-1] = actor;
		production[actor-1]++;
		ArrayList<Integer> scenes = roleToScenes.get(role-1);
		for (int scene : scenes) {
			actorsInScene.get(scene).add(actor);
		}
	}

	/**
	 * Remove the actor for the role given as argument.
	 */
	private void unassign(int role) {
		int actor = casting[role-1];
		casting[role-1] = 0;
		production[actor-1]--;
		for (int scene : roleToScenes.get(role-1)) {
			actorsInScene.get(scene).remove(actor);
		}
	}

	/**
	 * Returns true if the role given as argument has been
	 * assigned an actor which is not a super actor.
	 */
	private boolean hasActor(int role) {
		if (casting[role-1] > 0) return true;
		return false;
	}

	/**
	 * Returns true if the actor given as argument is playing
	 * in this production.
	 */
	private boolean inProduction(int actor) {
		return production[actor-1] > 0 ? true : false;
	}

	/**
	 * Mark the role given as argument to be played by a super actor.
	 */
	private void markWithSuperActor(int role) {
		casting[role-1] = SUPER_ACTOR;
	}

	/**
	 * Local search with two roles.
	 * @return True if a collision was found, false otherwise
	 */
	private boolean loc2search() {
		int r1 = random.nextInt(casting.length) + 1; // draw random sample
		int r2 = random.nextInt(casting.length) + 1;

		if (r1 == r2) return false;
		if (getActor(r1) == getActor(r2)) return false;
		if (getActor(r1) == SUPER_ACTOR || getActor(r2) == SUPER_ACTOR) return false;
		if (r1 == divaRoles[1] || r1 == divaRoles[2]) return false;
		if (r2 == divaRoles[1] || r2 == divaRoles[2]) return false;
		if (inSameScene(r1, r2)) return false;

		HashSet<Integer> r1s = roleToActorSet.get(r1-1);
		HashSet<Integer> r2s = roleToActorSet.get(r2-1);
		Integer[] r1a = roleToActorArray.get(r1-1);
		Integer[] r2a = roleToActorArray.get(r2-1);

		ArrayList<Integer> commonActors = intersect(r1a, r2a, r1s, r2s);

		for (int commonActor : commonActors) {
			if (!inProduction(commonActor)) continue;

			if (tryAssign(r1, commonActor) && tryAssign(r2, commonActor)) {
				assign(r1, commonActor);
				assign(r2, commonActor);
				return true;
			}
		}

		return false;
	}

	/**
	 * Find the intersection of two arrays.
	 * @return A list of the elements residing in both arrays
	 */
	private ArrayList<Integer> intersect(Integer[] a, Integer[] b, HashSet<Integer> as, HashSet<Integer> bs) {
		ArrayList<Integer> intersection = new ArrayList<Integer>(Math.min(a.length, b.length));

		if (a.length < b.length) {
			for (int i = 0; i < a.length; i++) {
				if (bs.contains(a[i])) intersection.add(a[i]);
			}
		} else {
			for (int i = 0; i < b.length; i++) {
				if (as.contains(b[i])) intersection.add(b[i]);
			}
		}

		return intersection;
	}

	/**
	 * Patch an existing solution to make it valid. This will replace duplicates and divas
	 * playing in the same scene with super actors. The solution might not be very good but
	 * it should pass all tests on Kattis. Patching a random assigment will give you a score
	 * of about 800 on Kattis.
	 * @deprecated
	 */
	private void patch() {
		// Make sure the divas are in the production
		assignDivas();

		for (Integer[] scene : sceneToRoleArray) {
			int[] fixRoles = new int[3]; // fixRoles[i] contains the role dedicated to diva i by assignDivas() or zero
			LinkedList<Integer> d1s = new LinkedList<Integer>(); // roles assigned to diva 1
			LinkedList<Integer> d2s = new LinkedList<Integer>(); // roles assigned to diva 2
			LinkedList<Integer> duplicates = new LinkedList<Integer>(); // roles which are duplicates
			HashSet<Integer> controlSet = new HashSet<Integer>();
			// ---------------------------------------------
			// collect
			for (int role : scene) {
				if (getActor(role) == 0) {
					markWithSuperActor(role);
					continue;
				}
				if (superActor(role)) {
					continue;
				}
				if (role == divaRoles[1] || role == divaRoles[2]) {
					fixRoles[getActor(role)] = role;
					continue;
				}
				if (hasDiva(role)) {
					// Add 
					if (getActor(role) == 1) d1s.add(role);
					else if (getActor(role) == 2) d2s.add(role);
					continue;
				}
				if (!controlSet.add(getActor(role))) {
					duplicates.add(role);
					continue;
				}
			}
			// ----------------------------------------------
			// resolve
			// An actor may only have one role in a scene
			for (int duplicate : duplicates) {
				markWithSuperActor(duplicate);
			}
			// Divas cannot play together
			if (fixRoles[1] != 0 || fixRoles[2] != 0) {
				// One of the roles in fixRoles is (and must be) played by a diva, remove the rest
				for (int diva2 : d2s) {
					markWithSuperActor(diva2);
				}
				for (int diva1 : d1s) {
					markWithSuperActor(diva1);
				}
				continue;
			}
			if (d1s.isEmpty() && d2s.isEmpty()) {
				// No divas
				continue;
			}
			if (d1s.isEmpty()) {
				// Keep one of the divas in d2s and remove the rest
				d2s.remove();
				for (int diva2 : d2s) {
					markWithSuperActor(diva2);
				}
				continue;
			}
			if (d2s.isEmpty()) {
				// Keep one of the divas in d1s and remove the rest
				d1s.remove();
				for (int diva1 : d1s) {
					markWithSuperActor(diva1);
				}
				continue;
			}
			// Both diva 1 and diva 2 play in this scene, keep first diva 1 and remove the rest
			d1s.remove();
			for (int diva1 : d1s) {
				markWithSuperActor(diva1);
			}
			for (int diva2 : d2s) {
				markWithSuperActor(diva2);
			}
		}
	}
}