package dk.brics.tajs.lattice;

public interface Joinable<T extends Joinable<T>> {
  public T join(T other);
}
