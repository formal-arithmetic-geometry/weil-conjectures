# Module.finiteProjectiveCokernel_residue_localization_of_finite

## Reason

Retire the item listed in coord/retire-items.tsv without losing its finite-source
extension. The old Sheaf module declares the same fully qualified theorem name as
WeilConjectures.RingTheory.FiniteProjectiveCokernelLocalization, but its source need
only be finite. Upstream additionally requires `[Module.Projective R P₁]`.
Importing both modules therefore creates a declaration-name collision.

The remaining direct consumer applies the stronger theorem to the finite image of
a differential. An isolated upstream-only import replacement was compiled through
lcompile.py and fails at the application (line 262):

```text
failed to synthesize instance of type class
  Module.Projective R ↥d.range
```

This is the actual compiler failure from the weaker specialization. This image is
not known projective before localization, so replacing
its import by upstream alone would fail instance synthesis. Preserve the complete,
already proved extension under the distinct name below in a new Sheaf module;
withdraw the old colliding module. The statement, proof, definitions and target
statements retain exactly their meanings. No source-library file changes.

## Old

Module: Sheaf.RingTheory.FiniteProjectiveCokernelLocalization

```lean
theorem finiteProjectiveCokernel_residue_localization
    {R : Type u} [CommRing R]
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂]
    [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (φ.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f))) ∧
        Module.Projective (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (φ.baseChange (Localization.Away f)))
```

## New

Module: Sheaf.RingTheory.FiniteSourceProjectiveCokernelLocalization

```lean
theorem finiteProjectiveCokernel_residue_localization_of_finite
    {R : Type u} [CommRing R]
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂]
    [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (φ.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f))) ∧
        Module.Projective (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (φ.baseChange (Localization.Away f)))
```

The new module preserves both proved private helpers and the entire theorem proof.
The old module is listed in deleted.txt and is withdrawn by the delivery tool.
The upstream projective-source specialization keeps its original name and signature.
The existing DAG node points at the stronger extension, since pointing it at the
weaker upstream specialization would silently change its finite-source statement.

## Users

`tools/downstream.py Sheaf.RingTheory.FiniteProjectiveCokernelLocalization --uses
Module.finiteProjectiveCokernel_residue_localization` lists the following two
transitive consumers. The sole direct import and application are adapted together.
No group holds either consumer in the current claims directory.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FiniteProjectiveCokernelLocalization | K3 | Withdrawn; removes the colliding declaration. |
| Sheaf.RingTheory.FiniteSourceProjectiveCokernelLocalization | new, K3 | Same finite-source theorem and proof, distinct name. |
| Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero | unclaimed | Change one proof import and the single theorem application; every signature and definition stays identical. |
| Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero | unclaimed | No source change needed; compiled against the adapted consumer. |

The upstream ResidueBottomDifferential already imports the upstream specialization;
it is untouched. The older retirement table's second Sheaf consumer is no longer
present. A whole-tree import/reference search finds no other users of the old module.

## Status

landed 20261020T135414-L-1819976 2026-10-20 (merge of deliver/K3/Sheaf.RingTheory.FiniteProjectiveCokernelLocalization)
