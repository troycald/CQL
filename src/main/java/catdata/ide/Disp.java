package catdata.ide;

public interface Disp {

  void close();

  default Throwable exn() {
    return null;
  }

}
