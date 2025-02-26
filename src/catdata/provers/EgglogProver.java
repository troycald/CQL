
package catdata.provers;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import catdata.Chc;
import catdata.Pair;
import catdata.Util;
import catdata.cql.AqlOptions;
import catdata.cql.AqlProver.ProverName;
import catdata.cql.Collage;
import catdata.cql.Collage.CCollage;
import catdata.cql.Constraints;
import catdata.cql.DP;
import catdata.cql.ED;
import catdata.cql.Instance;
import catdata.cql.Term;
import catdata.cql.fdm.InitialAlgebra;
import catdata.cql.fdm.SaturatedInstance;

public class EgglogProver<T, C, V> extends DPKB<T, C, V> {

	BufferedReader reader;
	BufferedWriter writer;
	BufferedReader err;
	Process proc;
	int runLevel;

	String it = "";
	String ot = "";
	int count = 0;

	// TODO CQL empty sorts check
	public EgglogProver(String exePath, KBTheory<T, C, V> th, int r) {
		super(th);

		runLevel = r;

		String sb = toEgglog(th);

		File f = new File(exePath);
		if (!f.exists()) {
			throw new RuntimeException("File does not exist: " + exePath);
		}

		try {
			String str = exePath;
			proc = Runtime.getRuntime().exec(str);

			writer = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));

			reader = new BufferedReader(new InputStreamReader(proc.getInputStream()));

			err = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			it = sb;

			writer.write(sb.toString() + "\n");
//			System.out.println(sb.toString());

		} catch (IOException e) {
			e.printStackTrace();
			throw new RuntimeException("1Internal theorem prover anomaly: " + e.getLocalizedMessage());
		}
	}

	public static String toEgglog(Constraints eds, Instance I) {
		StringBuffer sb = new StringBuffer();

		Function<Chc<String, String>, String> pr = z -> z.toString().replace("inr ", "").replace("inl ", "");
		Function<Map<String, Chc<String, String>>, String> qr = z -> {
			String ret = "";
			for (var w : z.entrySet()) {
				var d = " (univ" + pr.apply(w.getValue()) + " " + w.getKey() + ") ";
				ret += d;
			}
			return ret;
		};

		for (ED ed : eds.eds) {
			String tail = "";
			// String s1 = qr.apply(ed.As);
			// String s2 = qr.apply(ed.Es);
			// if (!s1.isEmpty()) {
			// tail = s1 + " " + s2;
			// }
			// tail = tail == "" ? "" : " :when (" + tail + ")";

			String lhs = "";
			String rhs = "";

			for (var eq : ed.Awh) {
				lhs += "(= " + eq.first.toEgglog() + " " + eq.second.toEgglog() + ")";
			}
			for (var eq : ed.Ewh) {
				rhs += "(union " + eq.first.toEgglog() + " " + eq.second.toEgglog() + ")";
			}

			sb.append("\n(rule (" + lhs + ") " + "(" + rhs + ") " + tail + ")");

		}
		if (I == null) {
			return toEgglog(eds.schema.collage().toKB()) + sb.toString();
		}

		var x = toEgglog(I.collage().toKB()) + sb.toString();
		System.out.println(x);
		return x;
	}

	private static <Ty, En, Sym, Fk, Att, Gen, Sk, X, Y> String readX(String s,
			Instance<Ty, En, Sym, Fk, Att, Gen, Sk, X, Y> I) {
		var i = s.trim().indexOf(" ");
		var j = s.trim().indexOf(")");
		return s.trim().substring(i+2, s.trim().length()-2);
	}

	
	public static <Ty, En, Sym, Fk, Att, Gen, Sk, X, Y> SaturatedInstance<Ty, En, Sym, Fk, Att, String, String, Integer, Chc<String, Pair<Integer, Att>>> egglogChase(
			String exePath, Constraints eds, Instance<Ty, En, Sym, Fk, Att, Gen, Sk, X, Y> I, AqlOptions ops) {

		String sb = toEgglog(eds, I);

		File f = new File(exePath);
		if (!f.exists()) {
			throw new RuntimeException("File does not exist: " + exePath);
		}

		try {
			String str = exePath;
			var proc = Runtime.getRuntime().exec(str);

			var writer = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
			var reader = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			var err = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			writer.write(sb.toString() + "\n");

			writer.write("(run-schedule (saturate (run)))" + "\n");

			writer.flush();

			while (true) {
				String w = err.readLine();
				System.out.println("***" + w);
				if (w.contains("Ruleset : search ")) {

					break;
				}
			}
			System.out.println("1------");
			try {
				Thread.currentThread().sleep(400);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			Function<String, Term<Ty, En, Sym, Fk, Att, Gen, Sk>> parseTerm = null;

//			Map<En, Collection<Term<Ty, En, Sym, Fk, Att, Gen, Sk>>> ens1 = new HashMap<>();
//			Map<En, Map<Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Map<Fk, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>>> fks1 = new HashMap<>();
//			Map<En, Map<Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Map<Att, Term<Ty, Void, Sym, Void, Void, Void, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>>>> atts1 = new HashMap<>();

			Collage<Ty, En, Sym, Fk, Att, String, String> col = new CCollage<>();
			col.addAll(I.schema().typeSide.collage());
			col.addAll(I.schema().collage());
			col.addAll((Collage)I.collage());
			
			
			Map<En, Integer> sizes = new HashMap<>();
			for (var en : I.schema().ens) {
				writer.write("(print-size " + "univ" + en + ")\n");
				writer.flush();
				String i = reader.readLine();

				int j = Integer.parseInt(i);
				sizes.put(en, j);
//				List<Term<Ty, En, Sym, Fk, Att, Gen, Sk>> l = new LinkedList<>();
//				ens1.put(en, l);
//				Map<Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Map<Att, Term<Ty, Void, Sym, Void, Void, Void, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>>> r = new HashMap<>();
//				atts1.put(en, r);
//				Map<Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Map<Fk, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>> r2 = new HashMap<>();
//				fks1.put(en, r2);

				writer.write("(print-function " + "univ" + en + " " + j + ")\n");
				writer.flush();

			//	reader.readLine(); // ?
				reader.readLine(); // (
				for (int w = 0; w < j; w++) {
					String k = reader.readLine();
					System.out.println("&" + k);
					var h = readX(k, I);
					col.gens().put(h, en);
					System.out.println("Adding " + h);
//					l.add(h);
//					r.put(h, new HashMap<>());
//					r2.put(h, new HashMap<>());

				}
				reader.readLine(); // )
			}
			/*
			 * System.out.println("2------"); for (var fk : I.schema().fks.entrySet()) {
			 * writer.write("(print-size " + fk.getKey() + ")\n"); writer.flush(); String i
			 * = reader.readLine();
			 * 
			 * int j = Integer.parseInt(i); writer.write("(print-function " + fk.getKey() +
			 * " " + j + ")\n"); writer.flush(); reader.readLine(); // ( for (int w = 0; w <
			 * j; w++) { String k = reader.readLine(); System.out.println("&"+ k); }
			 * reader.readLine(); // ) }
			 */
		/*	System.out.println("3------");

			for (var fk : I.schema().atts.entrySet()) {
				int j = sizes.get(I.schema().atts.get(fk.getKey()).first);
				writer.write("(print-function " + fk.getKey() + " " + j + ")\n");
				writer.flush();
				reader.readLine(); // ?
				reader.readLine(); // (

				for (int w = 0; w < j; w++) {
					String k = reader.readLine();
					System.out.println("^" + k);
					var m = readAtt(k, I);
//					col.atts().put(fk.getKey(), null);
				//	atts1.get(I.schema().atts.get(fk.getKey()).first).get(m.first).put(fk.getKey(), lift(m.second, I));
				}
				reader.readLine(); // )
			} */

			
			DP<Ty, En, Sym, Fk, Att, String, String> dp = new DP<>() {

				@Override
				public String toStringProver() {
					return "Egglog-chase";
				}

				@Override
				public boolean eq(Map<String, Chc<Ty, En>> ctx, Term<Ty, En, Sym, Fk, Att, String, String> lhs,
						Term<Ty, En, Sym, Fk, Att, String, String> rhs) {
					if (ctx != null && !ctx.isEmpty()) {
						throw new RuntimeException("Cannot solve full word problem");
					}
					try {

//						System.out.println("writing ")
						writer.write("(check (= " + lhs.toEgglog() + " " + rhs.toEgglog() + "))\n");
						writer.flush();

						// String s1 = reader.readLine();
						// System.out.println(s1);
						while (true) {
							String w = err.readLine();
							// System.out.println(w);
							if (w.contains("Check failed")) {
								return false;
							} else if (w.contains("Checked fact")) {
								return true;
							}
						}

					} catch (IOException e) {
						throw new RuntimeException(e);
					}
				}
				
			};

			var ret = new InitialAlgebra<Ty, En, Sym, Fk, Att, String, String>(ops, I.schema(), col, z -> z.toString(),
					(z, zz) -> z.toString(), dp, ProverName.egglog);

			
			var w = new SaturatedInstance<>(ret, ret, false, false, true, new HashMap<>());
			return w;
	
		//	return null;
			/*
			Function<En, Collection<Term<Ty, En, Sym, Fk, Att, Gen, Sk>>> ens = x -> ens1.get(x);
			BiFunction<En, Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Map<Fk, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>> fks = (x,
					y) -> new HashMap<>(); // (x,y) -> { throw new RuntimeException(); }
			Map<Ty, Collection<Term<Ty, En, Sym, Fk, Att, Gen, Sk>>> tys = (Map<Ty, Collection<Term<Ty, En, Sym, Fk, Att, Gen, Sk>>>) (Object) Util
					.newListsFor(I.schema().typeSide.tys);
			Collection<Eq<Ty, Void, Sym, Void, Void, Void, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>> eqs = new LinkedList<>();

			BiFunction<En, Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Map<Att, Term<Ty, Void, Sym, Void, Void, Void, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>>> atts = null;
			
			var alg = new ImportAlgebra<Ty, En, Sym, Fk, Att, Term<Ty, En, Sym, Fk, Att, Gen, Sk>, Term<Ty, En, Sym, Fk, Att, Gen, Sk>>(
					I.schema(), ens, tys, fks, atts, (x, y) -> "", (x, y) -> "", false, eqs);

			var w = new SaturatedInstance<>(alg, alg, false, false, true, new HashMap<>());
*/
		} catch (IOException e) {
			e.printStackTrace();
			throw new RuntimeException("1Internal theorem prover anomaly: " + e.getLocalizedMessage());
		}

	}

	public static <T, C, V> String toEgglog(KBTheory<T, C, V> th) {
		StringBuffer sig = new StringBuffer();
		StringBuffer ground = new StringBuffer();
		StringBuffer eqs = new StringBuffer();
		StringBuffer univ = new StringBuffer();
		StringBuffer univR = new StringBuffer();

		Map<T, List<String>> outer = Util.newListsFor(th.tys);
		Map<T, List<String>> outer2 = Util.newListsFor(th.tys);

		Function<T, String> pr = z -> z.toString().replace("inr ", "").replace("inl ", "");

		sig.append("(datatype*");
		for (C c : th.syms.keySet()) {
			var ty = th.syms.get(c);
			String s = "(" + c + " "
					+ Util.sep(ty.first.stream().map(j -> pr.apply(j)).collect(Collectors.toList()), " ") + ")";
			outer.get(ty.second).add(s);
			if (ty.first.isEmpty()) {
				ground.append("(" + c + ")\n");
			}
		}

		for (T ty : th.tys) {
			sig.append("\n(" + pr.apply(ty) + "\n" + Util.sep(outer.get(ty), "\n") + ")");
			univ.append("\n(relation univ" + pr.apply(ty) + " (" + pr.apply(ty) + "))");
		}
		eqs.append("\n");
		for (C c : th.syms.keySet()) {
			var ty = th.syms.get(c);
			String cc = "";
			for (int i = 1; i <= ty.first.size(); i++) {
				cc += (" var" + i + " ");
			}
			String s = "(rule ((= var0 (" + c + " " + cc.trim() + "))) ((univ" + pr.apply(ty.second) + " var0)))";
			outer2.get(ty.second).add(s);

		}
		sig.append("\n)");
		for (T ty : th.tys) {
			univR.append("\n" + Util.sep(outer2.get(ty), "\n"));

		}

		Function<Map<V, T>, String> qr = z -> {
			String ret = "";
			for (var w : z.entrySet()) {
				var d = "(univ" + pr.apply(w.getValue()) + " " + w.getKey() + ")";
				ret += d;
			}
			return ret;
		};
		for (var eq : th.eqs) {
			String tail = eq.first == null || eq.first.isEmpty() ? "" : " :when (" + qr.apply(eq.first) + ")";
			if (eq.first != null && eq.first.size() > 0) {
				eqs.append("\n(birewrite " + eq.second.toEgglog() + " " + eq.third.toEgglog() + tail + ")");
			} else {
				eqs.append("\n(union " + eq.second.toEgglog() + " " + eq.third.toEgglog() + ")");
			}

		}

		return sig.toString() + "\n" + ground.toString() + "\n" + univ + "\n" + univR + "\n" + eqs.toString() + "\n";
	}

	@Override
	public synchronized boolean eq(Map<V, T> ctx, KBExp<C, V> lhs, KBExp<C, V> rhs) {
		if (ctx != null && !ctx.isEmpty()) {
			throw new RuntimeException("Cannot solve full word problem");
		}
		try {
			writer.write("(run " + runLevel + " :until (= " + lhs.toEgglog() + " " + rhs.toEgglog() + "))" + "\n");
			writer.flush();

//			System.out.println("writing ")
			writer.write("(check (= " + lhs.toEgglog() + " " + rhs.toEgglog() + "))\n");
			writer.flush();

			// String s1 = reader.readLine();
			// System.out.println(s1);
			while (true) {
				String w = err.readLine();
				// System.out.println(w);
				if (w.contains("Check failed")) {
					return false;
				} else if (w.contains("Checked fact")) {
					return true;
				}
			}

		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public String toString() {
		var g = it + "\n\n" + ot;
		return "Egglog prover\n\n" + g.substring(0, Integer.min(g.length(), 4096 * 4096));
	}

	@Override
	public void add(C c, T t) {
		throw new RuntimeException("Not supported yet");
	}

	@Override
	public boolean supportsTrivialityCheck() {
		return false;
	}

}
