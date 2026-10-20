# AlgebraicGeometry.Scheme.affine_koszul_section_roof

## Reason

Restore the quarantined import path recorded in coord/rework.tsv. Its original
mixed import environment imported both Sheaf and upstream versions of derived
tensor augmentation and K-flat theory. The adopted upstream module already
contains the complete section-roof proof, with the same hypotheses and conclusion.
Keeping the duplicate declaration would recreate the collision. Restore the Sheaf
module as a public import of that proved upstream module, and attach the existing
DAG node to the upstream declaration. This is a restoration, not a withdrawal:
the quarantine archive is untouched, deleted.txt is not used, and the module still
provides the theorem to its importers. No upstream file is edited.

## Old

Quarantined module Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof:

```lean
theorem affine_koszul_section_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj,
      ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
        CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
        ∃ (u : J ⟶ T) (ξ : DerivedCategory.Q.obj J ⟶ E.obj),
          IsIso (R.map (DerivedCategory.Q.map u)) ∧
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ
```

Its public imports were WeilConjectures.AlgebraicGeometry.PerfectComplex,
Sheaf.AlgebraicGeometry.DerivedTensorAugmentation and
Mathlib.AlgebraicGeometry.AffineScheme. Its private proof imports included
Sheaf.Algebra.Homology.KFlatResolution and the upstream section-colimit theorem.

## New

The restored module publicly imports
WeilConjectures.AlgebraicGeometry.AffineKoszulSectionRoof, which provides:

```lean
theorem affine_koszul_section_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj,
      ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
        ∃ (u : J ⟶ T) (ξ : DerivedCategory.Q.obj J ⟶ E.obj),
          IsIso (R.map (DerivedCategory.Q.map u)) ∧
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ
```

IsKFlatTensor and the archived IsAcyclicTensorKFlat have identical definition
bodies, binders and universes. An independent Lean check recreated the archived
predicate under a private fresh name and proved the complete archived roof
signature by exact application of the upstream theorem. Thus the name change
changes no mathematical hypothesis or conclusion. The restriction functors,
chosen localization universes, compactness, quasi-coherence, perfectness,
augmentation, isomorphism and final equation all remain identical.
The node keeps its mathematical statement, proof steps, dependencies, and unit;
only its lean attachment points to the canonical existing theorem.
No target statement or target-used definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof | E1 | Restore as public upstream re-export; no duplicate declaration. |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed; quarantined rework item | Archived import path and theorem name remain available; archive untouched. Its independent restoration remains assigned through rework.tsv. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed upstream; unchanged | Already uses the canonical theorem. A sandbox copy with only its roof import redirected through the restored Sheaf path compiles. |

A scan of all current lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf
sources finds no other import or call to the Sheaf roof module. The only
DAG Lean attachment is updated. The parent lem-sc-affine-perfect-tensor-roof
retains its dependency and uses the same theorem; the unit route is preserved.
References in the colimit and spectrum-comparison nodes are blueprint provenance,
not reverse proof dependencies. tools/downstream.py cannot inventory the original
because its source is quarantined (unknown module), so the inventory above uses
an explicit source scan, including the quarantine directory.
There are no forced adaptations to another group's module.

## Status

landed 20261020T155630-L-3269109 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof)
