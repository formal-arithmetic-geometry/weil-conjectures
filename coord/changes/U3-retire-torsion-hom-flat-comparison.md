# LinearMap.baseChange_bijective_of_ideal_power_torsion

## Reason

The assigned module is listed as a retire item in `coord/retire-items.tsv`.
Its adopted upstream twin already proves precisely the same theorem under the same
fully qualified name. The inventory's DIFFERENT classification is due to binder names:
`_hflat`, `_hI`, `_hquot`, `_hK` versus `hflat`, `hI`, `hquot`, `hK`.
After this renaming, the signature text is identical. The proof bodies are also
identical after this renaming. Retain the upstream declaration verbatim, redirect
the sole Sheaf consumer's proof import, withdraw the duplicate Sheaf module,
and point the existing node's Lean attachment to the upstream declaration.

## Old

```lean
theorem baseChange_bijective_of_ideal_power_torsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {K : Type w} {N : Type x} [AddCommGroup K] [AddCommGroup N]
    [Module R K] [Module R N]
    (_hK : ∀ k : K, ∃ n : ℕ, ∀ r ∈ I ^ n, r • k = 0) :
    Function.Bijective (LinearMap.baseChange S : (K →ₗ[R] N) →
      (S ⊗[R] K →ₗ[S] S ⊗[R] N))
```

Module: `Sheaf.RingTheory.TorsionHomFlatComparison`, namespace `LinearMap`.

## New

```lean
theorem baseChange_bijective_of_ideal_power_torsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {K : Type w} {N : Type x} [AddCommGroup K] [AddCommGroup N]
    [Module R K] [Module R N]
    (hK : ∀ k : K, ∃ n : ℕ, ∀ r ∈ I ^ n, r • k = 0) :
    Function.Bijective (LinearMap.baseChange S : (K →ₗ[R] N) →
      (S ⊗[R] K →ₗ[S] S ⊗[R] N))
```

Module: `WeilConjectures.RingTheory.TorsionHomFlatComparison`, namespace `LinearMap`.
This is an existing upstream declaration; no upstream source is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TorsionHomFlatComparison | U3 | Withdraw redundant declaration and module. |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | unclaimed | Replace one proof import with the upstream twin; both theorem applications and all public signatures remain verbatim. |

`tools/downstream.py --uses` reports only these two modules and one downstream
module. A library-wide import search confirms the sole direct consumer is
`Sheaf.RingTheory.TorsionExtensionFlatDescent`. Existing upstream importers already
use the upstream theorem and are unchanged. No target statement or definition changes.

## Status

landed 20261020T141318-L-2036531 2026-10-20 (merge of deliver/U3/Sheaf.RingTheory.TorsionHomFlatComparison)
