package catdata.cql.exp;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import catdata.Pair;
import catdata.Util;
import catdata.cql.AqlOptions;
import catdata.cql.Instance;
import catdata.cql.Kind;
import catdata.cql.AqlOptions.AqlOption;
import catdata.cql.fdm.CqlPivot;

public final class InstExpPivot<Gen, Sk, X, Y> extends InstExp<X, Y, X, Y> {

  public <R, P, E extends Exception> R accept(P param, InstExpVisitor<R, P, E> v) throws E {
    return v.visit(param, this);
  }

  @Override
  public void mapSubExps(Consumer<Exp<?>> f) {
    I.map(f);
  }

  @Override
  public String toString() {
    return "pivot " + I;
  }

  public InstExpPivot(InstExp<Gen, Sk, X, Y> i, List<Pair<String, String>> ops) {
    I = i;
    this.ops = Util.toMapSafely(ops);
  }

  @Override
  public Collection<InstExp<?, ?, ?, ?>> direct(AqlTyping G) {
    return Collections.singleton(I);
  }

  public final InstExp<Gen, Sk, X, Y> I;
  public final Map<String, String> ops;

  @Override
  public SchExp type(AqlTyping G) {
    return new SchExpPivot<>(I, Collections.emptyList());
  }

  @Override
  protected Map<String, String> options() {
    return ops;
  }

  @Override
  protected void allowedOptions(Set<AqlOption> set) {
    set.add(AqlOption.require_consistency);
    set.add(AqlOption.allow_java_eqs_unsafe);
  }

  @Override
  public synchronized Instance<String, String, Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, X, Y, X, Y> eval0(
      AqlEnv env, boolean isC) {
    if (isC) {
      throw new IgnoreException();
    }
    AqlOptions strat = new AqlOptions(ops, env.defaults);
    Instance<String, String, Sym, catdata.cql.exp.Fk, catdata.cql.exp.Att, X, Y, X, Y> l = new CqlPivot<>(
        I.eval(env, false), strat).J;
    return l;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((I == null) ? 0 : I.hashCode());
    result = prime * result + ((ops == null) ? 0 : ops.hashCode());
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
    InstExpPivot<?, ?, ?, ?> other = (InstExpPivot<?, ?, ?, ?>) obj;
    if (I == null) {
      if (other.I != null)
        return false;
    } else if (!I.equals(other.I))
      return false;
    if (ops == null) {
      if (other.ops != null)
        return false;
    } else if (!ops.equals(other.ops))
      return false;
    return true;
  }

  @Override
  public Collection<Pair<String, Kind>> deps() {
    return I.deps();
  }

}