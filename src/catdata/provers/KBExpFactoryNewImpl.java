package catdata.provers;

import java.util.List;

import catdata.Chc;
import catdata.cql.Head;
import catdata.cql.Term;


public class KBExpFactoryNewImpl<Ty, En, Sym, Fk, Att, Gen, Sk>
    implements KBExpFactory<Chc<Ty, En>, Head<Ty, En, Sym, Fk, Att, Gen, Sk>, String> {

  public final static KBExpFactory factory = new KBExpFactoryNewImpl();

  private KBExpFactoryNewImpl() {
  }

  @Override
  public KBExp<Head<Ty, En, Sym, Fk, Att, Gen, Sk>, String> KBApp(Head<Ty, En, Sym, Fk, Att, Gen, Sk> c,
      List<KBExp<Head<Ty, En, Sym, Fk, Att, Gen, Sk>, String>> in) {
    List<Term<Ty, En, Sym, Fk, Att, Gen, Sk>> l = (List<Term<Ty, En, Sym, Fk, Att, Gen, Sk>>) (Object) in;
    return Term.Head(c, l);
  }

  @Override
  public KBExp<Head<Ty, En, Sym, Fk, Att, Gen, Sk>, String> KBVar(String v) {
    return Term.Var(v);
  }

  @Override
  public KBExp freshConst(Chc<Ty, En> o, int n) {
    if (!o.left) {
      return Term.Gen(Head.GenHead(new CC(n)));
    }
    return Term.Sk(Head.SkHead(new CC(n)));
  }

  private class CC {
    public final int i;

    public CC(int i) {
      // Util.assertNotNull(i);
      this.i = i;
    }

    @Override
    public int hashCode() {
      return i;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) {
        return true;
      }
      if (getClass() != o.getClass()) {
        return false;
      }
      return i == ((CC) o).i;
    }
  }

}
