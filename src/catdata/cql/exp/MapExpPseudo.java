package catdata.cql.exp;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import catdata.Pair;
import catdata.cql.ColimitSchema;
import catdata.cql.Kind;
import catdata.cql.Mapping;
import catdata.cql.AqlOptions.AqlOption;

public class MapExpPseudo extends MapExp {

	@Override
	public void mapSubExps(Consumer<Exp<?>> f) {
		exp.map(f);
	}

	@Override
	public <R, P, E extends Exception> MapExp coaccept(P params, MapExpCoVisitor<R, P, E> v, R r) throws E {
		return v.visitMapExpColim(params, r);
	}

	public <R, P, E extends Exception> R accept(P params, MapExpVisitor<R, P, E> v) throws E {
		return v.visit(params, this);
	}

	public final ColimSchExp exp;

	@Override
	public Map<String, String> options() {
		return Collections.emptyMap();
	}

	public MapExpPseudo(ColimSchExp exp) {
		this.exp = exp;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((exp == null) ? 0 : exp.hashCode());
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
		MapExpPseudo other = (MapExpPseudo) obj;
		if (exp == null) {
			if (other.exp != null)
				return false;
		} else if (!exp.equals(other.exp))
			return false;
		return true;
	}

	@Override
	public Pair<SchExp, SchExp> type(AqlTyping G) {
		try {
			SchExp dst = new SchExpColim(exp);
			SchExp src = new SchExpPseudo(exp);
			return new Pair<>(dst, src);
		} catch (Exception ex) {
			ex.printStackTrace();
			throw new RuntimeException(ex.getMessage() + "\n\n In " + this);
		}
	}

	@Override
	public Mapping<String, String, Sym, Fk, Att, String, Fk, Att> eval0(AqlEnv env, boolean isC) {
		Map<String, Mapping<String, String, Sym, Fk, Att, String, Fk, Att>> z = exp.eval(env, isC).mappingsStr;

		ColimitSchema<String> x = exp.eval(env, isC);
		if (x.fromPsuedo == null) {
			throw new RuntimeException("Not a pseudo colimit: " + x);
		}
		return x.fromPsuedo;

	}

	@Override
	public String toString() {
		return "getPseudo " + exp;
	}

	@Override
	public Collection<Pair<String, Kind>> deps() {
		return exp.deps();
	}

	@Override
	protected void allowedOptions(Set<AqlOption> set) {
	}

}