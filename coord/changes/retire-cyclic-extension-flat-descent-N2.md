# LinearMap.exists_cyclic_extension_flat_descent

## Reason

Listed retirement in `coord/retire-items.tsv`, authorized by the human in
`coord/changes/retire-sheaf-twins-20261020.md`. The duplicate has zero holes.
The upstream twin has the same theorem, with hypothesis binder names changed.
The only direct consumer applies it positionally. The prerequisite retirement of
`Sheaf.RingTheory.IdealPowerHomLift` is already landed. No upstream file changes.

## Old

`lean/Sheaf/RingTheory/CyclicExtensionFlatDescent.lean` declares:

```lean
theorem exists_cyclic_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (_hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    {T : Type x} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (R ⧸ I ^ n))
    (_ha : Function.Injective a) (_hab : Function.Exact a b)
    (_hb : Function.Surjective b) :
    ∃ (E : Type (max u w)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] (R ⧸ I ^ n)),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (j.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S
```

The consumer privately imports `Sheaf.RingTheory.CyclicExtensionFlatDescent`.

## New

Withdraw the duplicate using `deleted.txt`. Use the existing upstream theorem:

```lean
theorem exists_cyclic_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    {T : Type x} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (R ⧸ I ^ n))
    (ha : Function.Injective a) (hab : Function.Exact a b)
    (_hb : Function.Surjective b) :
    ∃ (E : Type (max u w)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] (R ⧸ I ^ n)),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (j.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S
```

The consumer privately imports `WeilConjectures.RingTheory.CyclicExtensionFlatDescent`.
The DAG attachment points to that declaration, with its exact upstream signature.
The mathematical statement, all five proof steps and their dependencies are preserved.
No definition, public consumer signature, target statement or unit route changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | unclaimed | Replace the private import on line 11; proof and signature unchanged. |

`tools/downstream.py --uses exists_cyclic_extension_flat_descent` lists this sole
consumer. Its actual positional call is unchanged. The import closure replaces
exactly the duplicate by its upstream twin, and adds no pair of Sheaf/upstream
modules with the same suffix. The DAG parent
`lem-weil-pbc-torsion-extension-flat-descent` still uses this same node and theorem.
Quarantined references and parents are checked separately; no dependency is dropped.
The adapted consumer compiles against the upstream theorem.

## Status

landed 20261020T155827-L-3293948 2026-10-20 (merge of deliver/N2/Sheaf.RingTheory.CyclicExtensionFlatDescent)
