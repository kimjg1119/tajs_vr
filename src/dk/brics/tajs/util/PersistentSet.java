package dk.brics.tajs.util;

import java.util.Collection;
import java.util.stream.Stream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Objects;
import java.util.function.Predicate;

public interface PersistentSet<V> extends Iterable<V>, DeepImmutable {

  PersistentSet<V> add(V value);

  boolean contains(V value);

  PersistentSet<V> remove(V value);

  PersistentSet<V> union(PersistentSet<V> other);

  PersistentSet<V> subtract(PersistentSet<V> other);

  boolean isEmpty();

  int size();

  boolean containsAll(PersistentSet<V> other);

  HashSet<V> toMutableSet();

  Stream<V> stream();

  PersistentSet<V> addAll(Collection<V> values);

  PersistentSet<V> retainAll(Collection<?> var1);

  PersistentSet<V> removeAll(Collection<?> var1);

  PersistentSet<V> removeIf(Predicate<? super V> filter);

  static <V> PersistentSet<V> empty() {
    return new MergeableSet<>();
  }
}

class MergeableSet<V> implements PersistentSet<V> {
  private final HashSet<V> set;

  public MergeableSet() {
    set = new HashSet<>();
  }

  public MergeableSet(Collection<? extends V> c) {
    set = new HashSet<>(c);
  }

  @Override
  public MergeableSet<V> add(V value) {
    HashSet<V> newSet = new HashSet<>(set);
    newSet.add(value);
    return this;
  }

  @Override
  public boolean contains(V value) {
    return set.contains(value);
  }

  @Override
  public MergeableSet<V> remove(V value) {
    HashSet<V> newSet = new HashSet<>(set);
    newSet.remove(value);
    return this;
  }

  @Override
  public MergeableSet<V> union(PersistentSet<V> other) {
    MergeableSet<V> otherSet = (MergeableSet<V>) other;
    HashSet<V> newSet = new HashSet<>(set);
    newSet.addAll(otherSet.set);
    return this;
  }

  @Override
  public boolean isEmpty() {
    return set.isEmpty();
  }

  @Override
  public int size() {
    return set.size();
  }

  @Override
  public boolean containsAll(PersistentSet<V> other) {
    MergeableSet<V> otherSet = (MergeableSet<V>) other;
    return set.containsAll(otherSet.set);
  }

  @Override
  public java.util.Iterator<V> iterator() {
    return set.iterator();
  }

  @Override
  public HashSet<V> toMutableSet() {
    return new HashSet<>(set);
  }

  @Override
  public Stream<V> stream() {
    return set.stream();
  }

  @Override
  public MergeableSet<V> addAll(Collection<V> values) {
    HashSet<V> newSet = new HashSet<>(set);
    newSet.addAll(values);
    return this;
  }

  @Override
  public MergeableSet<V> removeIf(Predicate<? super V> filter) {
    HashSet<V> newSet = new HashSet<>(set);
    newSet.removeIf(filter);
    return this;
  }

  @Override
  public MergeableSet<V> retainAll(Collection<?> c) {
    HashSet<V> newSet = new HashSet<>(set);
    newSet.retainAll(c);
    return this;
  }

  @Override
  public MergeableSet<V> removeAll(Collection<?> c) {
    HashSet<V> newSet = new HashSet<>(set);
    newSet.removeAll(c);
    return this;
  }

  @Override
  public MergeableSet<V> subtract(PersistentSet<V> other) {
    MergeableSet<V> otherSet = (MergeableSet<V>) other;
    HashSet<V> newSet = new HashSet<>(set);
    newSet.removeAll(otherSet.set);
    return this;
  }
}