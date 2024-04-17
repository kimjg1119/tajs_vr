package dk.brics.tajs.util;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

import dk.brics.tajs.lattice.Joinable;

public interface PersistentMap<K, V extends Joinable<V>> extends DeepImmutable, Joinable<PersistentMap<K, V>> {

  PersistentMap<K, V> put(K key, V value);

  PersistentMap<K, V> weakUpdate(K key, V value);

  V get(K key);

  boolean containsKey(K key);

  PersistentMap<K, V> remove(K key);

  @Override
  PersistentMap<K, V> join(PersistentMap<K, V> other);

  int size();

  default boolean isEmpty() {
    return this.size() == 0;
  }
}

class MergeableMap<K, V extends Joinable<V>> implements PersistentMap<K, V> {
  private final Map<K, V> map;

  public MergeableMap() {
    this.map = new HashMap<>();
  }

  private MergeableMap(Map<K, V> existingMap) {
    this.map = new HashMap<>(existingMap);
  }

  @Override
  public PersistentMap<K, V> put(K key, V value) {
    Map<K, V> newMap = new HashMap<>(this.map);
    newMap.put(key, value);
    return new MergeableMap<>(newMap);
  }

  @Override
  public PersistentMap<K, V> weakUpdate(K key, V value) {
    Map<K, V> newMap = new HashMap<>(this.map);
    if (!newMap.containsKey(key)) {
      newMap.put(key, value);
    } else {
      V oldValue = newMap.get(key);
      newMap.put(key, oldValue.join(value));
    }
    return new MergeableMap<>(newMap);
  }

  @Override
  public V get(K key) {
    return this.map.get(key);
  }

  @Override
  public boolean containsKey(K key) {
    return this.map.containsKey(key);
  }

  @Override
  public PersistentMap<K, V> remove(K key) {
    Map<K, V> newMap = new HashMap<>(this.map);
    newMap.remove(key);
    return new MergeableMap<>(newMap);
  }

  @Override
  public int size() {
    return this.map.size();
  }

  @Override
  public PersistentMap<K, V> join(PersistentMap<K, V> other) {
    MergeableMap<K, V> otherMap = (MergeableMap<K, V>) other;
    Map<K, V> newMap = new HashMap<>(this.map);
    for (K key : otherMap.map.keySet()) {
      V value = otherMap.map.get(key);
      if (newMap.containsKey(key)) {
        V oldValue = newMap.get(key);
        newMap.put(key, oldValue.join(value));
      } else {
        newMap.put(key, value);
      }
    }
    return new MergeableMap<>(newMap);
  }

}
