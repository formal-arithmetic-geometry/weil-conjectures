# AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_closedStalk

## Reason

The item is a retirement row with zero current holes. Its source is already a withdrawn
stub, but its DAG node and two DAG parents still require the original small representative
colimit. The adopted theorem uses strictLocalization and strictLocalizationToBase, so the
old withdrawal does not discharge that statement. Preserve it under a distinct smallModel_
name in StrictLocalSmallModel.BaseChangeClosedStalk, keeping the collision retired.

The canonical small-to-full colimit isomorphism and its structural-map equation give a
short complete transport proof from the adopted closed-stalk theorem. No new hypothesis,
weaker conclusion, changed definition, chosen witness, or target change is involved.

## Old

Current item source, verbatim:

```lean
module

/-! Withdrawn: no declarations remain; use the official WeilConjectures twin. -/
```

Its still-attached original small-model signature, verbatim:

```lean
theorem isIso_strictHenselization_baseChange_closedStalk {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) {A : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (eA : Spec (.of A) ≅ strictHenselizationScheme s) {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A)) (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s)) {k : Type u} [Field k] [IsSepClosed k] (a : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) : IsIso ((pointSmallEtale (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))
```

## New

The old module remains explicitly withdrawn through deleted.txt. The replacement module
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeClosedStalk publicly imports
StrictHenselizationStructuralMap, BaseChange.Derived and Mathlib.RingTheory.Henselian
from WeilConjectures. Its proof privately imports the adopted ClosedStalk theorem and
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison. The signature is:

```lean
theorem smallModel_isIso_strictHenselization_baseChange_closedStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    {k : Type u} [Field k] [IsSepClosed k]
    (a : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso ((pointSmallEtale
      (a ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))
```

Except for its distinct name, this is exactly the original attached signature. Compose eA
with Spec of the inverse canonical colimit comparison, rewrite its bottom map using
smallStrictHenselizationColimitIso_toBase, and apply the adopted closed-stalk theorem to
the same square. Proof irrelevance identifies its commutativity witness. The original node
keeps its natural-language statement, dependencies of the statement, and unit; only its
Lean attachment and proof route change. A source-attachment node records the existing
full-model theorem. No adopted declaration, attribute, signature, or import is changed.

The replacement compiles without errors or warnings in 7.1 seconds (an independent
initial compile also passed in 7.5 seconds). A temporary consumer with exactly the original
signature, with both the replacement and adopted theorem imported, compiles cleanly in
2.1 seconds. Printed axioms of the replacement, adopted theorem and structural-map
comparison are exactly propext, Classical.choice and Quot.sound. The consumer is excluded
from the delivered Lean tree; its source is retained in scratchpad/ClosedStalkConsumer.lean.txt.

## Users

The downstream.py --uses census reports zero direct or transitive Lean importers. The
two consumers listed in the retirement row are both already withdrawn stubs. Their DAG
proofs cite the unchanged original node id, so that mathematical dependency is preserved.
The current adopted consumers import the adopted theorem and need no edit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | C3 dispatch | Keep the collision retired; preserve its original statement in the replacement module. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeClosedStalk | new, C3 | Complete small-model transport proof; zero holes. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed, withdrawn stub | No current import or call to adapt; its original DAG dependency still has the exact required statement. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed, withdrawn stub | No current import or call to adapt; its original DAG dependency still has the exact required statement. |

No held module is adapted, no parent node is detached, and no node is deleted. The unit
sk-thm-p1 statement and realized steps are unchanged.

## Status

landed 20261023T230512-L-3435947 2026-10-23 (merge of deliver/C3/Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk)
