package dk.brics.tajs.util;

import java.util.HashSet;

interface PersistentSet<V> {

  PersistentSet<V> add(V value);

  boolean contains(V value);

  PersistentSet<V> remove(V value);

  PersistentSet<V> join(PersistentSet<V> other);

  int size();
}

class MergeableSet<V> implements PersistentSet<V> {
  private final HashSet<V> set;

  public MergeableSet() {
    set = new HashSet<>();
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
  public MergeableSet<V> join(PersistentSet<V> other) {
    MergeableSet<V> otherSet = (MergeableSet<V>) other;
    HashSet<V> newSet = new HashSet<>(set);
    newSet.addAll(otherSet.set);
    return this;
  }

  @Override
  public int size() {
    return set.size();
  }
}