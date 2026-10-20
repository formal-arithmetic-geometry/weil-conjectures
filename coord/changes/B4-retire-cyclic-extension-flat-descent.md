# LinearMap.exists_cyclic_extension_flat_descent

## Reason

Retirement assigned in coord/retire-items.tsv, under the human authorization in
coord/changes/retire-sheaf-twins-20261020.md. The Sheaf module has zero holes and
duplicates the proved official theorem. Its apparent API difference consists only
of underscore prefixes on hypothesis binder names. No source-library file changes.

## Old

lean/Sheaf/RingTheory/CyclicExtensionFlatDescent.lean declares:

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

The sole direct consumer privately imports Sheaf.RingTheory.CyclicExtensionFlatDescent.

## New

Withdraw the duplicate Sheaf module via deleted.txt and attach its existing DAG node
to lean/WeilConjectures/RingTheory/CyclicExtensionFlatDescent.lean, which declares:

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

The consumer privately imports WeilConjectures.RingTheory.CyclicExtensionFlatDescent.
Its positional application, public signature, proof and public imports stay identical.
The theorem has the same universes, hypotheses and conclusion; no definition or target
statement changes, and the unit route and all mathematical dependencies are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CyclicExtensionFlatDescent | B4 | Withdraw duplicate; DAG points upstream. |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | C2 | Forced private import replacement at line 11; no other change. |

tools/downstream.py --uses exists_cyclic_extension_flat_descent finds exactly the
withdrawn module and its sole consumer. The retired prerequisite IdealPowerHomLift
already imports its official upstream replacement, so no additional retirement is needed.

Validation: the adapted consumer compiles cleanly (6.3 s); the official theorem
uses only propext, Classical.choice and Quot.sound. An isolated compile of the
original consumer against the empty retired module fails at 150:8 with
Unknown identifier exists_cyclic_extension_flat_descent. Only line 11 changes.
The consumer import closure replaces exactly the duplicate module by its official
twin and contains no Sheaf/upstream twin pair.

## Status

landed 20261020T163700-L-3784708 2026-10-20 (merge of deliver/B4/Sheaf.RingTheory.CyclicExtensionFlatDescent)
