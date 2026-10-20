# LinearMap.exists_torsion_extension_flat_descent

## Reason

Complete the retirement listed in `coord/retire-items.tsv` for
`Sheaf.RingTheory.TorsionExtensionFlatDescent`. Its only public declaration is already
proved in `WeilConjectures.RingTheory.TorsionExtensionFlatDescent`. Their signatures
agree modulo four hypothesis binder names: `_hflat`, `_hI`, `_hquot`, `_hQ` become
`hflat`, `hI`, `hquot`, `hQ`. All universes, hypotheses and conclusions agree.

## Old

Duplicate declaration in `Sheaf.RingTheory.TorsionExtensionFlatDescent`:

```lean
theorem exists_torsion_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map))
    {N : Type w} [AddCommGroup N] [Module R N]
    {Q : Type x} [AddCommGroup Q] [Module R Q]
    (_hQ : ∀ x : Q, ∃ n : ℕ, 1 ≤ n ∧ ∀ r ∈ I ^ n, r • x = 0)
    {M' : Type y} [AddCommGroup M'] [Module S M']
    (ι : S ⊗[R] N →ₗ[S] M')
    (π : M' →ₗ[S] S ⊗[R] Q)
    (_hι : Function.Injective ι) (_hιπ : Function.Exact ι π)
    (_hπ : Function.Surjective π) :
    ∃ (E : Type (max u w x)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] Q),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] M',
        θ.toLinearMap.comp (j.baseChange S) = ι ∧
        π.comp θ.toLinearMap = q.baseChange S
```

## New

Use the existing declaration of the same fully qualified name in
`WeilConjectures.RingTheory.TorsionExtensionFlatDescent`:

```lean
theorem exists_torsion_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map))
    {N : Type w} [AddCommGroup N] [Module R N]
    {Q : Type x} [AddCommGroup Q] [Module R Q]
    (hQ : ∀ x : Q, ∃ n : ℕ, 1 ≤ n ∧ ∀ r ∈ I ^ n, r • x = 0)
    {M' : Type y} [AddCommGroup M'] [Module S M']
    (ι : S ⊗[R] N →ₗ[S] M')
    (π : M' →ₗ[S] S ⊗[R] Q)
    (_hι : Function.Injective ι) (_hιπ : Function.Exact ι π)
    (_hπ : Function.Surjective π) :
    ∃ (E : Type (max u w x)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] Q),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] M',
        θ.toLinearMap.comp (j.baseChange S) = ι ∧
        π.comp θ.toLinearMap = q.baseChange S
```

Withdraw the Sheaf duplicate using `deleted.txt` and repoint the existing DAG node's
Lean attachment to the upstream theorem. The upstream file and the mathematical
proof dependencies stay unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | C2 | Withdraw duplicate declaration. |
| WeilConjectures.RingTheory.TorsionExtensionFlatDescent | unclaimed; unchanged | Existing proved replacement, checked from current source. |
| WeilConjectures.RingTheory.FormalGlueingEssentialSurjectivity | unclaimed; unchanged | DAG parent already imports and applies the upstream theorem; compiled unchanged. |

`tools/downstream.py` reports zero direct or transitive Lean importers of the Sheaf
module, and no external use of its declaration in that import closure. Searching
current Lean and quarantine sources finds no importer of the retiring module.
The DAG has one parent, `lem-weil-pbc-formal-glueing-essential-surjectivity`, whose
Lean attachment is already `WeilConjectures.RingTheory.FormalGlueingEssentialSurjectivity`.
That parent's import is already the upstream replacement. Retaining the same node
preserves its statement, all parent dependencies and the unit route.

Validation: an example with the entire old signature applies the upstream theorem;
the current upstream theorem and parent sources compile separately through lcompile.py.
The theorem and parent axiom probes are recorded in report.md.

## Returned landing repair

The reviewer passed delivery `afd4aa3de`, but its withdrawal overlapped B4's later
change `f550737119` to the duplicate's cyclic-descent import. The current source
now imports `WeilConjectures.RingTheory.CyclicExtensionFlatDescent`. Revalidated
that exact current duplicate, refreshed the upstream and parent source probes,
and reapplied the same retirement on the current fetched `sheaf-dag` base.
No upstream source or mathematical dependency is changed by this repair.

## Status

landed 20261020T211641-L-3483356 2026-10-20 (merge of deliver/C2/Sheaf.RingTheory.TorsionExtensionFlatDescent)
