package catdata.cql.exp;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import org.apache.commons.collections4.list.TreeList;

import catdata.InteriorLabel;
import catdata.LocStr;
import catdata.Pair;
import catdata.Quad;
import catdata.Raw;
import catdata.Util;
import catdata.cql.AqlOptions;
import catdata.cql.ColimitSchema;
import catdata.cql.Kind;
import catdata.cql.Schema;
import catdata.cql.AqlOptions.AqlOption;
import catdata.cql.exp.SchExp.SchExpVar;
import gnu.trove.map.hash.THashMap;
import gnu.trove.set.hash.THashSet;

public class ColimSchExpPseudo extends ColimSchExp implements Raw {

  @Override
  public <R, P, E extends Exception> R accept(P param, ColimSchExpVisitor<R, P, E> v) throws E {
    return v.visit(param, this);
  }

  @Override
  protected void allowedOptions(Set<AqlOption> set) {
    set.add(AqlOption.allow_java_eqs_unsafe);
  }

  private Map<String, List<InteriorLabel<Object>>> raw = new THashMap<>(Collections.emptyMap());

  @Override
  public Map<String, List<InteriorLabel<Object>>> raw() {
    return raw;
  }

  public final TyExp ty;

  public final Map<String, SchExp> nodes;

  public final Map<String, Quad<String, String, String, String>> eqEn;

  public final Set<Quad<String, Pair<String, String>, RawTerm, RawTerm>> eqTerms;


  @Override
  public Map<String, String> options() {
    return options;
  }

  public Map<String, String> options;

  public ColimSchExpPseudo(TyExp ty, List<LocStr> nodes,
      List<Pair<Integer, Pair<String, Quad<String, String, String, String>>>> eqEn,
      List<Pair<Integer, Quad<String, Pair<String,String>, RawTerm, RawTerm>>> eqTerms,
      List<Pair<String, String>> options) {
    this.ty = ty;
    this.nodes = new LinkedHashMap<>(nodes.size());
    
    this.eqEn = Util.toMapSafely(LocStr.proj2(eqEn));
    
    this.eqTerms = LocStr.proj2(eqTerms);
    this.options = Util.toMapSafely(options);
    for (LocStr n : nodes) {
      if (this.nodes.containsKey(n.str)) {
        throw new RuntimeException("In schema colimit " + this + " duplicate schema " + n
            + " - please create new schema variable if necessary.");
      }
      this.nodes.put(n.str, new SchExpVar(n.str));
    }

    List<InteriorLabel<Object>> f = new TreeList<>();
    for (Pair<Integer, Pair<String, Quad<String, String, String, String>>> p : eqEn) {
      f.add(new InteriorLabel<>("entities", p.second.second, p.first,
          x -> x.first + "." + x.second + " = " + x.third + "." + x.fourth).conv());
    }
    raw.put("entities", f);

    f = new TreeList<>();
    for (Pair<Integer, Quad<String, Pair<String, String>, RawTerm, RawTerm>> p : eqTerms) {
      f.add(new InteriorLabel<>("path eqs", p.second, p.first, x -> x.third + " = " + x.fourth).conv());
    }
    raw.put("eqs", f);

  }

  @Override
  public synchronized ColimitSchema<String> eval0(AqlEnv env, boolean isC) {
    Map<String, Schema<String, String, Sym, Fk, Att>> nodes0 = new THashMap<>();
    Set<String> ens = new THashSet<>(nodes.size());
    for (String n : nodes.keySet()) {
      SchExp w = nodes.get(n);
      Schema<String, String, Sym, Fk, Att> z = w.eval(env, isC);
      nodes0.put(n, z);
      ens.addAll(nodes0.get(n).ens.stream().map(x -> (n + "_" + x)).collect(Collectors.toSet()));
    }

    return new ColimitSchema<>(ty.eval(env, isC), nodes0, eqEn, eqTerms, 
        new AqlOptions(options, env.defaults));
  }

  @Override
  public String toString() {
    final StringBuilder sb = new StringBuilder();

      sb.append("pseudo_quotient ").append(Util.sep(nodes.keySet(), " + ")).append(" : ").append(this.ty).append(" ")
        .append(" {\n");

    if (!eqEn.isEmpty()) {
      sb.append("\tentity_isomorphisms");
  		sb.append(Util.sep(eqEn, "\n", " : ", x -> x.first + "." + x.second + " -> " + x.third + "." + x.fourth));
    }

    if (!eqTerms.isEmpty()) {
      sb.append("\tequations")
          .append(this.eqTerms.stream().map(x -> "forall " + x.first + ". " + x.third + " = " + x.fourth)
              .collect(Collectors.joining("\n\t\t", "\n\t\t", "\n")));
    }

    if (!options.isEmpty()) {
      sb.append("\toptions")
          .append(this.options.entrySet().stream().map(sym -> sym.getKey() + " = " + sym.getValue())
              .collect(Collectors.joining("\n\t\t", "\n\t\t", "\n")));
    }
    return sb.append("\n}").toString();
  }

  @Override
  public Collection<Pair<String, Kind>> deps() {
    Set<Pair<String, Kind>> ret = new THashSet<>();
    ret.addAll(ty.deps());
    for (SchExp v : nodes.values()) {
      ret.addAll(v.deps());
    }
    return ret;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((eqEn == null) ? 0 : eqEn.hashCode());
    result = prime * result + ((eqTerms == null) ? 0 : eqTerms.hashCode());
    result = prime * result + ((nodes == null) ? 0 : nodes.hashCode());
    result = prime * result + ((options == null) ? 0 : options.hashCode());
    result = prime * result + ((ty == null) ? 0 : ty.hashCode());
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
    ColimSchExpPseudo other = (ColimSchExpPseudo) obj;
    if (eqEn == null) {
      if (other.eqEn != null)
        return false;
    } else if (!eqEn.equals(other.eqEn))
      return false;
    if (eqTerms == null) {
      if (other.eqTerms != null)
        return false;
    } else if (!eqTerms.equals(other.eqTerms))
      return false;
    if (nodes == null) {
      if (other.nodes != null)
        return false;
    } else if (!nodes.equals(other.nodes))
      return false;
    if (options == null) {
      if (other.options != null)
        return false;
    } else if (!options.equals(other.options))
      return false;
    if (ty == null) {
      if (other.ty != null)
        return false;
    } else if (!ty.equals(other.ty))
      return false;
    return true;
  }

  @Override
  public SchExp getNode(String n, AqlTyping G) {
    return nodes.get(n);
  }

  @Override
  public Set<String> type(AqlTyping G) {
    ty.type(G);
    for (String n : nodes.keySet()) {
      TyExp w = nodes.get(n).type(G);
      if (!w.equals(ty)) {
        throw new RuntimeException("Schema for " + n + " is on typeside " + w + " and not on " + ty);
      }
    }
    return nodes.keySet();
  }

  @Override
  public Set<Pair<SchExp, SchExp>> gotos(ColimSchExp ths) {
    Set<Pair<SchExp, SchExp>> ret = new THashSet<>(nodes.size());
    SchExp t = new SchExpColim(ths);
    for (SchExp s : nodes.values()) {
      ret.add(new Pair<>(s, t));
    }
    return ret;
  }

  @Override
  public TyExp typeOf(AqlTyping G) {
    ty.type(G);
    for (String n : nodes.keySet()) {
      TyExp w = nodes.get(n).type(G);
      if (!w.equals(ty)) {
        throw new RuntimeException("Schema for " + n + " is on typeside " + w + " and not on " + ty);
      }
    }
    return ty;
  }

  @Override
  public void mapSubExps(Consumer<Exp<?>> f) {
    ty.map(f);
    for (SchExp x : nodes.values()) {
      x.map(f);
    }
  }

}