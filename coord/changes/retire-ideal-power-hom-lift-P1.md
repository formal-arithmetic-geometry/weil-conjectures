# LinearMap.exists_ideal_power_hom_lift

## Reason

Retirement item in `coord/retire-items.tsv`, authorized by the human in
`coord/changes/retire-sheaf-twins-20261020.md`. The Sheaf copy has zero holes and
duplicates the complete upstream theorem. The reported API difference consists only
of underscore prefixes on hypothesis binder names. Its only direct consumer applies
the theorem positionally, so replacing the proof import requires no proof edits.
The private Koszul helper has no external users.

## Old

`lean/Sheaf/RingTheory/IdealPowerHomLift.lean` declares:

```lean
theorem exists_ideal_power_hom_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (_hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    (d : ↥(I ^ n) →ₗ[R] S ⊗[R] N) :
    ∃ (l : ↥(I ^ n) →ₗ[R] N) (m : S ⊗[R] N),
      ∀ r : ↥(I ^ n), 1 ⊗ₜ[R] l r = d r + (r : R) • m
```

Its consumer imports `Sheaf.RingTheory.IdealPowerHomLift`.

## New

Withdraw `lean/Sheaf/RingTheory/IdealPowerHomLift.lean` via `deleted.txt`.
The unchanged official declaration in
`lean/WeilConjectures/RingTheory/IdealPowerHomLift.lean` is:

```lean
theorem exists_ideal_power_hom_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    (d : ↥(I ^ n) →ₗ[R] S ⊗[R] N) :
    ∃ (l : ↥(I ^ n) →ₗ[R] N) (m : S ⊗[R] N),
      ∀ r : ↥(I ^ n), 1 ⊗ₜ[R] l r = d r + (r : R) • m
```

The consumer instead imports `WeilConjectures.RingTheory.IdealPowerHomLift`.
The DAG attachment points to this upstream module and declaration. Its mathematical
statement, four proof steps, proof dependencies and unit route are unchanged.
No source-library file is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CyclicExtensionFlatDescent | unclaimed | Replace line 11's private import; statement and proof unchanged. |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | unclaimed | Transitive importer; unchanged, compiled against the adapted consumer. |

`tools/downstream.py --uses exists_ideal_power_hom_lift` finds only the cyclic
consumer outside the withdrawn module. Both consumers' import closures replace
exactly the Sheaf copy by its upstream twin; neither new closure contains any
Sheaf/upstream twin pair. Hypotheses, universes, conclusion and public statement
imports are the same. No definition or target statement changes.

## Status

landed 20261020T145534-L-2408894 2026-10-20 (merge of deliver/P1/Sheaf.RingTheory.IdealPowerHomLift)
