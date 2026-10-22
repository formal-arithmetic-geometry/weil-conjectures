# AlgebraicGeometry.tensorCounit_oneKFlat_coordinates

## Reason

The assigned module is absent from lean/ and retained in quarantine by the current
coord/rework.tsv assignment. The archive has zero holes. Compiling it unchanged fails
while elaborating its theorem signature: synthesis of the coproduct HasColimit needed
by mapBifunctor exceeds the typeclass heartbeat budget at line 159.

The adopted source already proves the same theorem under the same public name.
Restoring a second declaration would duplicate that name. Restore the old Sheaf module
path by publicly importing the source proof, retaining the original public canonical
comparison import. This is a restoration, not a withdrawal: the archive remains intact,
the theorem remains available, and its existing parent dependency and unit route remain.
No source-library file is changed.

The only substantive-looking signature difference is the K-flat predicate name:
IsAcyclicTensorKFlat in the archive, IsKFlatTensor upstream. Their full definitions have
the same type and body. The source also spells out the category argument of curriedTensor
where the archive uses an inferred argument. Neither difference changes the proposition. A mechanical comparison of the entire
signatures after these two substitutions and whitespace normalization finds no other
difference.
The sandbox consumer reproduces the archived theorem result, using local letI bindings
for the already available small colimits and total-complex existence proofs, and applies
the source theorem with the archived K-flat hypothesis. These bindings introduce no
hypothesis. The consumer compiled in 10.2 seconds and its axiom check, like the source
theorem axiom check, lists only propext, Classical.choice and Quot.sound. It separately checks the equality
of the two polymorphic K-flat definitions by rfl.

The DAG attachment is redirected to the actual source declaration with its source
signature recorded verbatim. Its statement, statement dependencies, proof, proof
dependencies and unit are unchanged. No target statement or definition is changed.

## Old

The module was absent from lean/. The quarantined public signature was:

```lean
theorem tensorCounit_oneKFlat_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (k : T ⟶ X)
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback k).obj (A ⊗ B) ⟶
        (derivedPullback k).obj A ⊗ (derivedPullback k).obj B)
    (hτ : IsCanonicalPullbackTensorComparison k τ) :
    ∃ a : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj G ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))),
      ∃ b : (DerivedCategory.Q
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj
            (CochainComplex.mapBifunctor P G
              (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≅
        (derivedPullback k).obj (DerivedCategory.Q.obj P) ⊗ (DerivedCategory.Q
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G),
        (derivedPullback k).map a.hom ≫
          (SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
              (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫ b.hom =
          τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj G) ≫
            (derivedPullback k).obj (DerivedCategory.Q.obj P) ◁
            (SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj G)
```

The archive had one public import:
`Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison`.
Its remaining imports were private proof imports.

## New

The complete restored compatibility module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.TensorCounitOneKFlatCoordinates

/-! # Tensor pullback counit in one K-flat coordinate

Compatibility import of the adopted source proof of
`AlgebraicGeometry.tensorCounit_oneKFlat_coordinates`. The source K-flat predicate
`IsKFlatTensor` agrees by reduction with the legacy `IsAcyclicTensorKFlat` predicate.
The canonical comparison import preserves the legacy statement vocabulary.

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-counit-one-kflat-coordinates).
-/

@[expose] public section

```

The public name refers to the existing adopted proof. No new theorem, axiom, instance,
choice of data or proof hole is introduced.

## Users

Because the module is absent, tools/downstream.py reports "unknown module(s)" for the
assigned path. Exact import and declaration searches were therefore also made in both
lean/ and quarantine/. There are no current library imports of the missing Sheaf path.
Its sole archived direct importer is listed below. It applies the theorem with an
IsAcyclicTensorKFlat hypothesis; the complete archived-signature consumer checks that
application. No archived importer uses private declarations from the item via import all.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | M4 | Restore the old import path. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | quarantined | Same theorem name and full legacy type; no adaptation. |
| WeilConjectures.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unchanged source | Already imports the adopted proof; no change. |

No forced adaptations are included. The existing DAG parent
lem-pc-rf-base-change-complex still cites this node and hence still uses the same result.

## Status

landed 20261022T002424-L-1928043 2026-10-22 (merge of deliver/M4/Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates)
