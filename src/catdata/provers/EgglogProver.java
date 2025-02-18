
package catdata.provers;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import catdata.Util;

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
	public EgglogProver(String exePath, KBTheory<T, C, V> th, int r, long timeout) {
		super(th);

		StringBuffer sb = new StringBuffer();
		StringBuffer sb2 = new StringBuffer();
		StringBuffer sb3 = new StringBuffer();
		runLevel = r;
		Map<T, List<String>> outer = Util.newListsFor(kb.tys);
		Map<T, List<String>> outer2 = Util.newListsFor(kb.tys);

		Function<T, String> pr = z -> z.toString().replace("inr ", "").replace("inl ", "");

		sb.append("(datatype*");
		for (C c : th.syms.keySet()) {
			var ty = th.syms.get(c);
			String s = "(" + c + " "
					+ Util.sep(ty.first.stream().map(j -> pr.apply(j)).collect(Collectors.toList()), " ") + ")";
			outer.get(ty.second).add(s);
			if (ty.first.isEmpty()) {
				sb3.append("(" + c + ")\n");
			}
		}

		for (T ty : th.tys) {
			sb.append("\n(" + pr.apply(ty) + "\n" + Util.sep(outer.get(ty), "\n") + ")");
			sb2.append("\n(relation univ" + pr.apply(ty) + " (" + pr.apply(ty) + "))");
		}
		sb2.append("\n");
		for (C c : th.syms.keySet()) {
			var ty = th.syms.get(c);
			String cc = "";
			for (int i = 1; i <= ty.first.size(); i++) {
				cc += (" var" + i + " ");
			}
			String s = "(rule ((= var0 (" + c + " " + cc.trim() + "))) ((univ" + pr.apply(ty.second) + " var0)))";
			outer2.get(ty.second).add(s);

		}
		sb.append("\n)");
		for (T ty : th.tys) {
			sb2.append(Util.sep(outer2.get(ty), "\n"));

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
			sb2.append("\n(birewrite " + eq.second.toEgglog() + " " + eq.third.toEgglog() + tail + ")");
		//	sb2.append("\n(birewrite " + eq.third.toEgglog() + " " + eq.second.toEgglog() + tail + ")");
			count++;

		}

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

			it = sb.toString();
			it += sb2.toString();

			writer.write(sb.toString() + "\n");
			System.out.println(sb.toString());
			writer.write(sb2.toString() + "\n");
			System.out.println(sb2.toString() + "\n");
			writer.write(sb3.toString() + "\n");
			System.out.println(sb3.toString() + "\n");

			


		} catch (IOException e) {
			e.printStackTrace();
			throw new RuntimeException("1Internal theorem prover anomaly: " + e.getLocalizedMessage());
		}
	}

	@Override
	public synchronized boolean eq(Map<V, T> ctx, KBExp<C, V> lhs, KBExp<C, V> rhs) {
		if (ctx == null || !ctx.isEmpty()) {
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
				System.out.println(w);
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
