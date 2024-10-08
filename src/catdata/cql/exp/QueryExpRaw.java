package catdata.cql.exp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import catdata.Chc;
import catdata.InteriorLabel;
import catdata.LocException;
import catdata.LocStr;
import catdata.Pair;
import catdata.Raw;
import catdata.Triple;
import catdata.Unit;
import catdata.Util;
import catdata.cql.AqlOptions;
import catdata.cql.Collage;
import catdata.cql.Eq;
import catdata.cql.Kind;
import catdata.cql.Query;
import catdata.cql.Schema;
import catdata.cql.Term;
import catdata.cql.Transform;
import catdata.cql.AqlOptions.AqlOption;
import catdata.cql.Collage.CCollage;
import catdata.cql.It.ID;
import catdata.cql.Query.Agg;
import gnu.trove.map.hash.THashMap;
import gnu.trove.set.hash.THashSet;

public class QueryExpRaw extends QueryExp implements Raw {

	@SuppressWarnings("unchecked")
	@Override
	public Collection<Exp<?>> imports() {
		return (Collection<Exp<?>>) (Object) imports;
	}

	@Override
	protected void allowedOptions(Set<AqlOption> set) {
		set.add(AqlOption.dont_validate_unsafe);
		set.add(AqlOption.query_remove_redundancy);
		set.addAll(AqlOptions.proverOptionNames());
	}

	@Override
	public <R, P, E extends Exception> R accept(P params, QueryExpVisitor<R, P, E> v) throws E {
		return v.visit(params, this);
	}

	private final SchExp src;
	private final SchExp dst;

	private final Set<QueryExp> imports;

	private final Map<String, String> options;

	private final Map<String, Block> blocks;

	public final Map<String, String> params;
	public final Map<String, RawTerm> consts;

	private final Map<String, Integer> b1 = new THashMap<>();
	private final Map<Fk, Integer> b2 = new THashMap<>();
	private final Map<Att, Integer> b3 = new THashMap<>();

	@Override
	public Map<String, String> options() {
		return options;
	}

	public static class Trans extends Exp<Void> implements Raw {

		@Override
		public Object type(AqlTyping G) {
			return Unit.unit;
		}

		private Map<String, List<InteriorLabel<Object>>> raw = new THashMap<>();

		@Override
		public Map<String, List<InteriorLabel<Object>>> raw() {
			return raw;
		}

		@Override
		protected Map<String, String> options() {
			return null;
		}

		@Override
		public Kind kind() {
			return null;
		}

		@Override
		public Void eval0(AqlEnv env, boolean isC) {
			return null;
		}

		@Override
		public Collection<Pair<String, Kind>> deps() {
			return null;
		}

		public final Set<Pair<String, RawTerm>> gens;

		public final Map<String, String> options;

		public Trans(List<Pair<LocStr, RawTerm>> gens, List<Pair<String, String>> options) {
			this.gens = new THashSet<>();
			for (Pair<LocStr, RawTerm> gen : gens) {
				this.gens.add(new Pair<>((gen.first.str), gen.second));
			}
			this.options = Util.toMapSafely(options);

			List<InteriorLabel<Object>> f = new LinkedList<>();
			for (Pair<LocStr, RawTerm> p : gens) {
				f.add(new InteriorLabel<>("generators", new Pair<>(p.first.str, p.second), p.first.loc,
						x -> x.first + " -> " + x.second).conv());
			}
			raw.put("generators", f);
		}

		@Override
		public int hashCode() {
			int prime = 31;
			int result = 1;
			result = prime * result + ((gens == null) ? 0 : gens.hashCode());
			result = prime * result + ((options == null) ? 0 : options.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			Trans other = (Trans) obj;
			if (gens == null) {
				if (other.gens != null)
					return false;
			} else if (!gens.equals(other.gens))
				return false;
			if (options == null) {
				if (other.options != null)
					return false;
			} else if (!options.equals(other.options))
				return false;
			return true;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("{");

			sb.append("")
					.append(this.gens.stream().map(en -> en.first + " -> " + en.second).collect(Collectors.joining("\n\t")));

			sb.append(" options ").append(this.options.entrySet().stream().map(opt -> Util.maybeQuote(opt.getKey()) + " = " + opt.getValue())
					.collect(Collectors.joining("\n\t")));

			sb.append("}");
			return sb.toString();
		}

		@Override
		public Exp<Void> Var(String v) {
			return null;
		}

		@Override
		protected void allowedOptions(Set<AqlOption> set) {

		}

		@Override
		public void mapSubExps(Consumer<Exp<?>> f) {

		}

	}

	public static class PreAgg {
		public final Pair<String, String> ctx;

		public final List<Pair<String, String>> lgens;

		public final List<Pair<RawTerm, RawTerm>> leqs;

		public final RawTerm ret, zero, op;

		public PreAgg(List<Pair<String, String>> lgens, List<Pair<RawTerm, RawTerm>> leqs, RawTerm ret, Pair<String, String> b,
				RawTerm zero, RawTerm op) {
			this.ctx = b;
			this.lgens = lgens;
			this.leqs = leqs;
			this.ret = ret;
			this.zero = zero;
			this.op = op;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((ctx == null) ? 0 : ctx.hashCode());
			result = prime * result + ((leqs == null) ? 0 : leqs.hashCode());
			result = prime * result + ((lgens == null) ? 0 : lgens.hashCode());
			result = prime * result + ((ret == null) ? 0 : ret.hashCode());
			result = prime * result + ((zero == null) ? 0 : zero.hashCode());
			result = prime * result + ((op == null) ? 0 : op.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			PreAgg other = (PreAgg) obj;
			if (ctx == null) {
				if (other.ctx != null)
					return false;
			} else if (!ctx.equals(other.ctx))
				return false;
			if (leqs == null) {
				if (other.leqs != null)
					return false;
			} else if (!leqs.equals(other.leqs))
				return false;
			if (lgens == null) {
				if (other.lgens != null)
					return false;
			} else if (!lgens.equals(other.lgens))
				return false;
			if (ret == null) {
				if (other.ret != null)
					return false;
			} else if (!ret.equals(other.ret))
				return false;
			if (zero == null) {
				if (other.zero != null)
					return false;
			} else if (!zero.equals(other.zero))
				return false;
			if (op == null) {
				if (other.op != null)
					return false;
			} else if (!op.equals(other.op))
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "from " + Util.sep(lgens.iterator(), " ", x -> x.first + ":" + x.second) + "\n\twhere "
					+ Util.sep(leqs.iterator(), "\t", x -> x.first + "=" + x.second) + "\n\treturn " + ret + "\n\taggregate "
					+ zero + "\n\tlambda " + ctx.first + " " + ctx.second + ". " + op;
		}

	}

	public static class PreBlock {
		public final List<Pair<LocStr, String>> gens;
		public final List<Pair<Integer, Pair<RawTerm, RawTerm>>> eqs;
		public final List<Pair<String, String>> options;
		public final List<Pair<LocStr, Chc<RawTerm, PreAgg>>> atts;
		public final List<Pair<LocStr, Trans>> fks;
		public final boolean star;

		public PreBlock(List<Pair<LocStr, String>> gens, List<Pair<Integer, Pair<RawTerm, RawTerm>>> eqs,
				List<Pair<LocStr, Chc<RawTerm, PreAgg>>> atts, List<Pair<LocStr, Trans>> fks,
				List<Pair<String, String>> options, boolean star) {
			this.gens = gens;
			this.eqs = eqs;
			this.atts = atts;
			this.fks = fks;
			this.options = options;
			this.star = star;
		}

	}

	public static class Block extends Exp<Void> implements Raw {

		@Override
		public Object type(AqlTyping G) {
			return Unit.unit;
		}

		public Map<String, List<InteriorLabel<Object>>> raw = new THashMap<>();

		@Override
		public Kind kind() {
			return null;
		}

		@Override
		public Void eval0(AqlEnv env, boolean isC) {
			return null;
		}

		@Override
		public Collection<Pair<String, Kind>> deps() {
			return null;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((atts == null) ? 0 : atts.hashCode());
			result = prime * result + ((en == null) ? 0 : en.hashCode());
			result = prime * result + ((eqs == null) ? 0 : eqs.hashCode());
			result = prime * result + ((fks == null) ? 0 : fks.hashCode());
			result = prime * result + ((gens == null) ? 0 : gens.hashCode());
			result = prime * result + ((options == null) ? 0 : options.hashCode());
			result = prime * result + (star ? 1231 : 1237);
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			Block other = (Block) obj;
			if (atts == null) {
				if (other.atts != null)
					return false;
			} else if (!atts.equals(other.atts))
				return false;
			if (en == null) {
				if (other.en != null)
					return false;
			} else if (!en.equals(other.en))
				return false;
			if (eqs == null) {
				if (other.eqs != null)
					return false;
			} else if (!eqs.equals(other.eqs))
				return false;
			if (fks == null) {
				if (other.fks != null)
					return false;
			} else if (!fks.equals(other.fks))
				return false;
			if (gens == null) {
				if (other.gens != null)
					return false;
			} else if (!gens.equals(other.gens))
				return false;
			if (options == null) {
				if (other.options != null)
					return false;
			} else if (!options.equals(other.options))
				return false;
			if (star != other.star)
				return false;
			return true;
		}

		public final boolean star;
		public final Set<Pair<Att, Chc<RawTerm, PreAgg>>> atts;
		public final Set<Pair<Fk, Trans>> fks;
		public String en;
		public final List<Pair<String, String>> gens;
		// public final Set<Pair<Var, Ty>> sks;
		public final Set<Pair<RawTerm, RawTerm>> eqs;
		public final Map<String, String> options;
		public final Integer enLoc;

		public Block(PreBlock b, LocStr en, boolean star) {
			this.en = (en.str);
			this.enLoc = en.loc;
			this.star = star;
			this.gens = new LinkedList<>();
			this.atts = LocStr.set2(b.atts).stream().map(x -> new Pair<>(Att.Att(this.en, x.first), x.second))
					.collect(Collectors.toSet());
			this.fks = LocStr.set2(b.fks).stream().map(x -> new Pair<>(Fk.Fk(this.en, x.first), x.second))
					.collect(Collectors.toSet());

			for (Pair<LocStr, String> gen : b.gens) {
				this.gens.add(new Pair<>((gen.first.str), gen.second));
			}
			this.eqs = LocStr.proj2(b.eqs);
			this.options = Util.toMapSafely(b.options);

			List<InteriorLabel<Object>> e = new ArrayList<>(b.gens.size());
			for (Pair<LocStr, String> p : b.gens) {
				e.add(new InteriorLabel<>("from", new Pair<>(p.first.str, p.second), p.first.loc,
						x -> x.first + " : " + x.second).conv());
			}
			this.raw.put("from", e);

			List<InteriorLabel<Object>> xx = new ArrayList<>(b.eqs.size());
			for (Pair<Integer, Pair<RawTerm, RawTerm>> p : b.eqs) {
				xx.add(new InteriorLabel<>("where", p.second, p.first, x -> x.first + " = " + x.second).conv());
			}
			this.raw.put("where", xx);

			xx = new ArrayList<>(b.atts.size());
			for (Pair<LocStr, Chc<RawTerm, PreAgg>> p : b.atts) {
				xx.add(new InteriorLabel<>("attributes", new Pair<>(p.first.str, p.second), p.first.loc,
						x -> x.first + " -> " + x.second.toStringMash()).conv());
			}
			raw.put("attributes", xx);

			xx = new LinkedList<>();
			for (Pair<LocStr, Trans> p : b.fks) {
				xx.add(new InteriorLabel<>("foreign_keys", new Pair<>(p.first.str, p.second), p.first.loc,
						x -> x.first + " -> " + x.second).conv());
			}
			raw.put("foreign_keys", xx);
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("\nentity ").append(this.en).append(" -> { ");

			if (!this.gens.isEmpty()) {
				final Map<String, Set<String>> x = Util.revS(Util.toMapSafely(this.gens));
				sb.append("\n\tfrom \n\t\t");
				sb.append(Util.alphabetical(x.keySet()).stream().map(en -> Util.sep(x.get(en), " ") + " : " + en)
						.collect(Collectors.joining("\n\t\t")));
			}

			if (!this.eqs.isEmpty()) {
				sb.append("\n\twhere\n\t\t");
				sb.append(Util.alphabetical(this.eqs).stream().map(sym -> sym.first + " = " + sym.second)
						.collect(Collectors.joining("\n\t\t")));
			}

			if (!this.atts.isEmpty()) {
				sb.append("\n\tattributes\n\t\t");
				if (star) {
					sb.append(" * ");
				}
				sb.append(Util.alphabetical(this.atts).stream().map(sym -> Util.maybeQuote(sym.first.str) + " -> " + sym.second.toStringMash())
						.collect(Collectors.joining("\n\t\t")));
			}

			if (!fks.isEmpty()) {
				sb.append("\n\tforeign_keys\n\t\t");
				sb.append(Util.alphabetical(this.fks).stream().map(sym -> sym.first + " -> " + sym.second)
						.collect(Collectors.joining("\n\t\t")));
			}

			if (!this.options.isEmpty()) {
				sb.append("\n\toptions \n\t\t");
				sb.append(this.options.entrySet().stream().map(sym -> sym.getKey() + " = " + sym.getValue())
						.collect(Collectors.joining("\n\t\t")));
			}

			sb.append("}");
			return sb.toString();
		}

		private String toString2;

		public synchronized String toString2() {
			if (toString2 != null) {
				return toString2;
			}
			toString2 = "";

			List<String> temp = new LinkedList<>();

			if (!gens.isEmpty()) {
				toString2 += "\t\t\t\tfrom ";

				Map<String, Set<String>> x = Util.revS(Util.toMapSafely(gens));
				temp = new LinkedList<>();
				for (String En : Util.alphabetical(x.keySet())) {
					temp.add(Util.sep(x.get(En), " ") + " : " + En);
				}

				toString2 += Util.sep(temp, "\n\t\t\t\t\t");
			}

			if (!eqs.isEmpty()) {
				toString2 += "\n\t\t\t\twhere\t";
				temp = new LinkedList<>();
				for (Pair<RawTerm, RawTerm> sym : Util.alphabetical(eqs)) {
					temp.add(sym.first + " = " + sym.second);
				}
				toString2 += Util.sep(temp, "\n\t\t\t\t\t");
			}

			if (!atts.isEmpty()) {
				toString2 += "\n\t\t\t\tattributes\t";
				if (star) {
					toString2 += " * ";
				}
				temp = new LinkedList<>();
				for (Pair<Att, Chc<RawTerm, PreAgg>> sym : Util.alphabetical(atts)) {
					temp.add(Util.maybeQuote(sym.first.str) + " -> " + sym.second.toStringMash());
				}
				toString2 += Util.sep(temp, "\n\t\t\t\t\t");
			}

			if (!fks.isEmpty()) {
				toString2 += "\n\t\t\t\tforeign_keys\t";
				temp = new LinkedList<>();
				for (Pair<catdata.cql.exp.Fk, Trans> sym : Util.alphabetical(fks)) {
					temp.add(sym.first.str + " -> {" + sym.second + "}");
				}
				toString2 += Util.sep(temp, "\n\t\t\t\t\t");
			}

			if (!options.isEmpty()) {
				toString2 += "\n\t\t\t\toptions ";
				temp = new LinkedList<>();
				for (Entry<String, String> sym : options.entrySet()) {
					temp.add(sym.getKey() + " = " + sym.getValue());
				}

				toString2 += "\n\t\t\t\t" + Util.sep(temp, "\n\t\t\t\t\t");
			}

			toString2 = "\t" + toString2;
			return toString2;
		}

		@Override
		public Map<String, List<InteriorLabel<Object>>> raw() {
			return raw;
		}

		@Override
		protected Map<String, String> options() {
			return options;
		}

		@Override
		public Exp<Void> Var(String v) {
			return null;
		}

		@Override
		protected void allowedOptions(Set<AqlOption> set) {

		}

		@Override
		public void mapSubExps(Consumer<Exp<?>> f) {

		}

	}

	@Override
	public int hashCode() {
		int prime = 31;
		int result = 1;
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		result = prime * result + ((consts == null) ? 0 : consts.hashCode());
		result = prime * result + ((blocks == null) ? 0 : blocks.hashCode());
		result = prime * result + ((dst == null) ? 0 : dst.hashCode());
		result = prime * result + ((imports == null) ? 0 : imports.hashCode());
		result = prime * result + ((options == null) ? 0 : options.hashCode());
		result = prime * result + ((src == null) ? 0 : src.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		QueryExpRaw other = (QueryExpRaw) obj;
		if (blocks == null) {
			if (other.blocks != null)
				return false;
		} else if (!blocks.equals(other.blocks))
			return false;
		if (dst == null) {
			if (other.dst != null)
				return false;
		} else if (!dst.equals(other.dst))
			return false;
		if (imports == null) {
			if (other.imports != null)
				return false;
		} else if (!imports.equals(other.imports))
			return false;
		if (options == null) {
			if (other.options != null)
				return false;
		} else if (!options.equals(other.options))
			return false;
		if (src == null) {
			if (other.src != null)
				return false;
		} else if (!src.equals(other.src))
			return false;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		if (consts == null) {
			if (other.consts != null)
				return false;
		} else if (!consts.equals(other.consts))
			return false;
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("literal : ");
		sb.append(this.src).append(" -> ").append(this.dst);
		sb.append(" {");

		if (!this.imports.isEmpty()) {
			sb.append("\nimports ").append(this.imports.stream().map(x -> x.toString()).collect(Collectors.joining("\n\t")));
		}

		sb.append(this.blocks.values().stream().map(x -> x.toString()).collect(Collectors.joining("\n\t")));

		if (!this.options.isEmpty()) {
			sb.append(" options ").append(this.options.entrySet().stream().map(sym -> sym.getKey() + " = " + sym.getValue())
					.collect(Collectors.joining("\n\t")));
		}

		return sb.toString() + "}";
	}

	public QueryExpRaw(List<Pair<LocStr, String>> params, List<Pair<LocStr, RawTerm>> consts, SchExp c, SchExp d,
			List<QueryExp> imports, List<Pair<LocStr, PreBlock>> list, List<Pair<String, String>> options) {
		this.src = c;
		this.dst = d;
		this.imports = new THashSet<>(imports);
		this.options = Util.toMapSafely(options);
		this.consts = new THashMap<>(Util.toMapSafely(LocStr.set2(consts)));
		this.params = new THashMap<>(Util.toMapSafely(LocStr.set2(params)));

		Set<Block> bb = Util.toSetSafely(list).stream().map(x -> new Block(x.second, x.first, x.second.star))
				.collect(Collectors.toSet());
		blocks = new THashMap<>();
		for (Block x : bb) {
			blocks.put(x.en, x);
		}

		for (Pair<LocStr, PreBlock> x : list) {
			String z = (x.first.str);
			if (x.second.star) {
				throw new RuntimeException("Cannot use * in non-simple queries");
			}
			b1.put(z, x.first.loc);

			for (Pair<LocStr, Trans> y : x.second.fks) {
				b2.put(Fk.Fk(z, y.first.str), y.first.loc);
			}

			for (Pair<LocStr, Chc<RawTerm, PreAgg>> y : x.second.atts) {
				b3.put(Att.Att(z, y.first.str), y.first.loc);
			}

			List<InteriorLabel<Object>> f = new LinkedList<>();

			f.add(new InteriorLabel<>("entities", blocks.get(z), x.first.loc, y -> x.first.str).conv());

			raw.put(x.first.str, f);
		}

	}

	private Map<String, List<InteriorLabel<Object>>> raw = new THashMap<>();

	@Override
	public Map<String, List<InteriorLabel<Object>>> raw() {
		return (raw);
	}

	@Override
	public Collection<Pair<String, Kind>> deps() {
		Collection<Pair<String, Kind>> ret = new THashSet<>(src.deps());
		ret.addAll(dst.deps());
		for (QueryExp x : imports) {
			ret.addAll(x.deps());
		}
		return ret;
	}

	@Override
	public Pair<SchExp, SchExp> type(AqlTyping G) {
		TyExp t1 = src.type(G);
		TyExp t2 = dst.type(G);
//		if (!t1.equals(t2)) {
//			throw new RuntimeException("Non-equal typesides: " + t1 + " and " + t2);
//		}
		
		return new Pair<>(src, dst);
	}

	@Override
	public synchronized Query<String, String, Sym, Fk, Att, String, Fk, Att> eval0(AqlEnv env, boolean isC) {
		if (!(boolean) env.defaults.getOrDefault(AqlOption.allow_aggregation_unsafe)) {
			for (Entry<String, Block> x : this.blocks.entrySet()) {
				for (Pair<Att, Chc<RawTerm, PreAgg>> w : x.getValue().atts) {
					if (!w.second.left) {
						throw new RuntimeException(
								"To enable aggregation, set allow_aggregation_unsafe=true globally.  Aggregation is not functorial.");
					}
				}
			}
		}
		
		Schema<String, String, Sym, Fk, Att> src0 = src.eval(env, isC);
		Schema<String, String, Sym, Fk, Att> dst0 = dst.eval(env, isC);

		Map<String, Triple<LinkedHashMap<String, Chc<String, String>>, Collection<Eq<String, String, Sym, Fk, Att, String, String>>, AqlOptions>> ens0 = new THashMap<>();
		Map<Att, Chc<Term<String, String, Sym, Fk, Att, String, String>, Agg<String, String, Sym, Fk, Att>>> atts0 = new THashMap<>();
		Map<Fk, Pair<Map<String, Term<Void, String, Void, Fk, Void, String, Void>>, AqlOptions>> fks0 = new THashMap<>();
		Map<Fk, Map<String, Term<String, String, Sym, Fk, Att, String, String>>> sks0 = new THashMap<>();

		Map<String, String> xxx = new THashMap<>();
		Map<String, Term<String, Void, Sym, Void, Void, Void, Void>> yyy = new THashMap<>();

		for (QueryExp k : imports) {
			Query<String, String, Sym, Fk, Att, String, Fk, Att> v = k.eval(env, isC);

			for (String var : v.params.keySet()) {
				xxx.put(var, v.params.get(var)); // allow benign collisions
			}
			for (String var : v.consts.keySet()) {
				yyy.put(var, v.consts.get(var));
			}
			for (String En : v.ens.keySet()) {
				Set<Pair<Term<String, String, Sym, Fk, Att, String, String>, Term<String, String, Sym, Fk, Att, String, String>>> x = v.ens
						.get(En).eqs;
				Collection<Eq<String, String, Sym, Fk, Att, String, String>> z = new ArrayList<>(x.size());
				for (Pair<Term<String, String, Sym, Fk, Att, String, String>, Term<String, String, Sym, Fk, Att, String, String>> a : x) {
					z.add(new Eq<>(null, a.first, a.second));
				}
				ens0.put(En, new Triple<>(Util.inLeftOrder(v.ens.get(En).gens, v.ens.get(En).order), z, v.ens.get(En).options));
			}
			for (Att Att : v.atts.keySet()) {
				if (!v.atts.get(Att).left) {
					Util.anomaly();
				}
				atts0.put(Att, v.atts.get(Att));
			}
			for (Fk Fk : v.fks.keySet()) {
				Transform<String, String, Sym, catdata.cql.exp.Fk, Att, String, String, String, String, ID, Chc<String, Pair<ID, Att>>, ID, Chc<String, Pair<ID, Att>>> w = v.fks
						.get(Fk);
				Map<String, Term<Void, String, Void, Fk, Void, String, Void>> m = new THashMap<>();
				w.src().gens().forEach((pp, qq) -> {
					m.put(pp, w.gens().apply(pp, qq));
				});

				fks0.put(Fk, new Pair<>(m, v.doNotValidate.get(Fk)));
			}

		}

		Map<String, Collage<String, String, Sym, Fk, Att, String, String>> cols = new THashMap<>();
		for (Block p : blocks.values()) {
			try {
				if (!dst0.ens.contains(p.en)) {
					throw new RuntimeException(
							"The proposed target entity " + p.en + " does not actually appear in the target schema");
				}
				processBlock(options, env, src0, ens0, cols, p, params);
			} catch (RuntimeException ex) {
				ex.printStackTrace();
				throw new LocException(b1.get(p.en), "In block for target entity " + p.en + ", " + ex.getMessage());
			}
			Set<String> set = new THashSet<>(p.gens.size());
			for (Pair<String, String> z : p.gens) {
				if (src0.typeSide.tys.contains((z.second))) {
					set.add(z.first);
				}
			}
			for (Pair<Att, Chc<RawTerm, PreAgg>> pp : p.atts) {
				try {
					processAtt(src0, dst0, ens0, atts0, cols, pp, params, set);
				} catch (Exception ex) {
					ex.printStackTrace();
					throw new LocException(b3.get(pp.first), "In return clause for " + pp.first + ", " + ex.getMessage());
				}
			}
		}

		// two loops bc need stuff in en to do this part
		for (Block p : blocks.values()) {
			Set<String> set = new THashSet<>();
			for (Pair<String, String> z : p.gens) {
				if (src0.typeSide.tys.contains((z.second))) {
					set.add(z.first);
				}
			}
			for (Pair<catdata.cql.exp.Fk, Trans> pp : p.fks) {
				try {
					Map<String, Term<String, String, Sym, Fk, Att, String, String>> sks = new THashMap<>();
					Map<String, Term<Void, String, Void, Fk, Void, String, Void>> trans = new THashMap<>();
					for (Pair<String, RawTerm> v : pp.second.gens) {
						var qqq = dst0.fks.get(pp.first);
						if (qqq == null) {
							throw new RuntimeException("Not a foreign key: " + pp.first);
						}
						// Map<String, Chc<String, catdata.aql.exp.Ty>> Map = (
						// ens0.get(qqq.first).first);
						// Map<String, Chc<Ty, String>> Map1 = Util.map(Map, (k, x) -> new Pair<>(k,
						// x.reverse()));
						Collage<String, String, Sym, Fk, Att, String, String> col = cols.get(dst0.fks.get(pp.first).first);
						Chc<String, String> required = ens0.get(dst0.fks.get(pp.first).second).first.get(v.first);
						if (required == null) {
							throw new RuntimeException("Not an entity or type: " + v.first);
						}
						Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> term = RawTerm
								.infer1x(Collections.emptyMap() /* Not Map1 */, v.second, null, required.reverse(),
										col.convert(), "in foreign key " + pp.first.str + ", ", src0.typeSide.js).second;
						Term<String, String, Sym, Fk, Att, String, String> l = term.convert();
						Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> r = Query
								.freeze(l, params, set);

						if (!r.hasTypeType()) {
							trans.put(v.first, r.convert());
						} else {
							sks.put(v.first, r);
						}
					}
//          boolean doNotCheckEqs = (Boolean)
//              .getOrDefault(AqlOption.dont_validate_unsafe);
//          System.out.println("++++++++" + doNotCheckEqs);
					fks0.put(pp.first, new Pair<>(trans, new AqlOptions(pp.second.options, env.defaults)));
					sks0.put(pp.first, sks);

				} catch (RuntimeException ex) {
					ex.printStackTrace();
					throw new LocException(b2.get(pp.first), ex.getMessage());
				}
			}
		}

		for (String s : params.keySet()) {
			xxx.put(s, params.get(s));
		}
		for (String s : consts.keySet()) {
			Chc<String, String> required = Chc.inLeft(xxx.get((s)));
			Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> term = RawTerm
					.infer1x(Collections.emptyMap(), consts.get(s), null, required, src0.collage().convert(), "",
							src0.typeSide.js).second;

			yyy.put((s), term.convert());
		}
		return Query.makeQuery2(xxx, yyy, ens0, atts0, fks0, sks0, src0, dst0,

				new AqlOptions(options, env.defaults));
	}

	public static synchronized void processAtt(Schema<String, String, Sym, Fk, Att> src0,
			Schema<String, String, Sym, Fk, Att> dst0,
			Map<String, Triple<LinkedHashMap<String, Chc<String, String>>, Collection<Eq<String, String, Sym, Fk, Att, String, String>>, AqlOptions>> ens0,
			Map<Att, Chc<Term<String, String, Sym, Fk, Att, String, String>, Agg<String, String, Sym, Fk, Att>>> atts0,
			Map<String, Collage<String, String, Sym, Fk, Att, String, String>> cols, Pair<Att, Chc<RawTerm, PreAgg>> pp,
			Map<String, String> params, Set<String> set) {
		Pair<String, String> z = dst0.atts.get(pp.first);
		if (z == null) {
			throw new RuntimeException("Not a target attribute: " + pp.first);
		}
		Triple<LinkedHashMap<String, Chc<String, String>>, Collection<Eq<String, String, Sym, Fk, Att, String, String>>, AqlOptions> www = ens0
				.get(z.first);
		{
			if (www == null) {
				throw new RuntimeException("Not an entity: " + dst0.atts.get(pp.first));
			}
		}
		Map<String, Chc<String, String>> Map = (www.first);
		Collage<String, String, Sym, Fk, Att, String, String> col = cols.get(dst0.atts.get(pp.first).first);
		Chc<String, String> required = Chc.inLeft(dst0.atts.get(pp.first).second);
		for (String q : params.keySet()) {
			String tt = (params.get(q));
			Map.put(q, Chc.inRight(tt));
			col.sks().put((q), tt);
		}
		Map<String, Chc<String, String>> ens1 = Util.map(Map, (y, x) -> new Pair<>(y, x.reverse()));

		if (pp.second.left) {
			Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> term = RawTerm
					.infer1x(Collections.emptyMap() /* not ens! */, pp.second.l, null, required, col.convert(), "",
							src0.typeSide.js).second;
			atts0.put(pp.first, Chc.inLeft(Query.freeze(term.convert(), params, set)));
		} else {
			PreAgg pre = pp.second.r;
			col = new CCollage<>(col);

			Map<String, Chc<String, String>> ens1x = new THashMap<>(ens1);
			ens1x.put(pre.ctx.first, required);
			ens1x.put(pre.ctx.second, required);
			Set<String> setq = new THashSet<>(set);
			setq.add((pre.ctx.first));
			setq.add((pre.ctx.second));

			Term<String, String, Sym, Fk, Att, String, String> zeroX = RawTerm.infer1x(ens1x, pre.zero, null, required,
					col.convert(), "", src0.typeSide.js).second;
			Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> zero = Query
					.freeze(zeroX.convert(), params, set);

			Term<String, String, Sym, Fk, Att, String, String> opX = RawTerm.infer1x(ens1x, pre.op, null, required,
					col.convert(), "", src0.typeSide.js).second;

			Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> op = Query
					.freezeAgg(opX.convert(), params, setq, pre.ctx.first, pre.ctx.second);

			Map<String, String> lfrom = new THashMap<>();
			// Map<String, Chc<Ty,String>> u = new THashMap<>(ens1);
			for (Pair<String, String> k : pre.lgens) {
				if (ens1.containsKey(k.first)) {
					throw new RuntimeException("Duplicate FROM variable: " + k.first);
				}
				String v = (k.first);
				if (lfrom.containsKey(v)) {
					throw new RuntimeException("Duplicate FROM variable: " + k.first);
				}
				String en = (k.second);
				lfrom.put(v, en);
				col.gens().put(k.first, en);
			}

			Term<String, String, Sym, Fk, Att, String, String> retX = RawTerm.infer1x(Collections.emptyMap() /* not u */,
					pre.ret, null, required, col.convert(), "", src0.typeSide.js).second;
			Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String> ret = Query
					.freeze(retX.convert(), params, set);

			Set<Pair<Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String>, Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String>>> lwhere = new THashSet<>();

			for (Pair<RawTerm, RawTerm> eq : pre.leqs) {
				// Term<Ty, En, Sym, Fk, Att, Gen, Sk>
				// eqX = RawTerm.infer1x(ens1x, eq.first, eq.second, required, col.convert(),
				// "", src0.typeSide.js).second;
				// Term<catdata.aql.exp.Ty, catdata.aql.exp.En, catdata.aql.exp.Sym,
				// catdata.aql.exp.Fk, catdata.aql.exp.Att, Var, Var>
				// eqY = Query.freeze(retX.convert(), params, set);

				Triple<Map<String, Chc<String, String>>, Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String>, Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String>> x = RawTerm
						.infer1x(Collections.emptyMap() /* not u */, eq.first, eq.second, null, col.convert(),
								"In equation " + eq.first + " = " + eq.second + ", ", src0.typeSide.js)
						.first3();
				lwhere.add(new Pair<>(Query.freeze(x.second.convert(), params, set),
						Query.freeze(x.third.convert(), params, set)));

			}

			Pair<String, String> ctx = new Pair<>((pre.ctx.first), (pre.ctx.second));

			Agg<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att> agg = new Agg<>(zero, op, lfrom,
					lwhere, ret, ctx);

			atts0.put(pp.first, Chc.inRight(agg));
		}
	}

	public static synchronized void processBlock(Map<String, String> options, AqlEnv env,
			Schema<String, String, Sym, Fk, Att> src0,
			Map<String, Triple<LinkedHashMap<String, Chc<String, String>>, Collection<Eq<String, String, Sym, Fk, Att, String, String>>, AqlOptions>> ens,
			Map<String, Collage<String, String, Sym, Fk, Att, String, String>> cols, Block p, Map<String, String> params) {
		Map<String, String> xx = Util.toMapSafely(p.gens);
		LinkedHashMap<String, Chc<String, String>> Map = new LinkedHashMap<>();
		Collage<String, String, Sym, Fk, Att, String, String> col = new CCollage<>(src0.collage());
		Set<String> set = new THashSet<>(p.gens.size());
		for (Pair<String, String> z : p.gens) {
			if (src0.typeSide.tys.contains((z.second))) {
				set.add(z.first);
			}
		}
		for (String v : xx.keySet()) {
			String en = (xx.get(v));
			String tt = (en);
			if (src0.ens.contains(en)) {
				Map.put(v, Chc.inLeft(en));
				col.gens().put(v, en);
			} else if (src0.typeSide.tys.contains(tt)) {
				Map.put(v, Chc.inRight(tt));
				col.sks().put(v, tt);
			} else {
				throw new RuntimeException("From clause contains " + v + ":" + en + ", but " + en
						+ " is not a source entity.  Available: " + Util.sep(src0.ens, ", ") + ". ");
			}
		}

		for (String q : params.keySet()) {
			String vv = (q);
			String tt = (params.get(q));
			Map.put(vv, Chc.inRight(tt));
			col.sks().put(vv, tt);
		}

		cols.put(p.en, col);
		Collection<Eq<String, String, Sym, Fk, Att, String, String>> eqs = new ArrayList<>(p.eqs.size());

		for (Pair<RawTerm, RawTerm> eq : p.eqs) {
			Triple<Map<String, Chc<String, String>>, Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String>, Term<String, String, catdata.cql.exp.Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, String, String>> x = RawTerm
					.infer1x(Collections.emptyMap() /* not Map! */, eq.first, eq.second, null, col.convert(),
							"In equation " + eq.first + " = " + eq.second + ", ", src0.typeSide.js)
					.first3();
			eqs.add(new Eq<>(null, Query.freeze(x.second.convert(), params, set),
					Query.freeze(x.third.convert(), params, set)));
		}
		Map<String, String> uu = new THashMap<>(options);
		uu.putAll(p.options);
		AqlOptions theops = new AqlOptions(uu, env.defaults);
		Triple<LinkedHashMap<String, Chc<String, String>>, Collection<Eq<String, String, Sym, Fk, Att, String, String>>, AqlOptions> b = new Triple<>(
				Map, eqs, theops);
		ens.put(p.en, b);
	}

	@Override
	public void mapSubExps(Consumer<Exp<?>> f) {
		this.src.map(f);
		this.dst.map(f);
	}

}
