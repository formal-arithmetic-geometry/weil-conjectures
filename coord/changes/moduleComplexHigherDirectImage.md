# AlgebraicGeometry.ProEtale.moduleComplexHigherDirectImage

## Reason

The available same-unit continuity theorem uses the module-valued derived direct image.
The old helper independently derived the underlying abelian direct image, making the
DAG's instruction to apply the existing theorem require a separate comparison.
Reuse the recorded module construction and forget scalars after homology. This is the
same mathematical higher direct image, including arbitrary ring sheaves and every
integer degree. Stacks Tag 0D6J, clause (3), identifies the two derived constructions;
exactness of forgetting scalars commutes it with homology. The canonical comparison
is preserved by naturality. Tag 0D6I gives the same cohomology-presheaf description.
The source texts read were sites-cohomology.tex, labels
lemma-modules-abelian-unbounded and lemma-unbounded-describe-higher-direct-images,
and sites-modules.tex, label lemma-limits-colimits (Tag 03DB).

Both bodies construct functors; neither has data left as sorry. The reused right-derived
functor is chosen by a universal property determining it up to its unit-compatible
unique isomorphism, as required by AGENTS.md. Its existing resolution-existence and
continuity theorems remain obligations of their original modules.

## Old

```lean
noncomputable def moduleComplexHigherDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (A : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) (q : ℤ) :
    CochainComplex (SheafOfModules.{u + 1} A) ℤ ⥤
      Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  let C := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}
  let D := Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} C
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} D
  (SheafOfModules.toSheaf.{u + 1} A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q ⋙
    (lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorOfQuasiIsoResolutions
      (fun L ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj L,
        (CochainComplex.toKInjectiveResolution.{u + 1} C).app L,
        inferInstance, (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C L).2⟩) ⋙
    DerivedCategory.homologyFunctor D q
```

The original public imports were:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
```

## New

```lean
noncomputable def moduleComplexHigherDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (A : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) (q : ℤ) :
    CochainComplex (SheafOfModules.{u + 1} A) ℤ ⥤
      Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage g A q ⋙
    SheafOfModules.toSheaf.{u + 1}
      ((Scheme.proEtaleSheafDirectImage g RingCat.{u + 1}).obj A)
```

The public imports are now:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
```

Both declaration signatures and visibility are identical. The theorem is now proved.
Redundant public imports are removed and the construction's module is public because
it occurs in the public definition's body. The colimit-preservation instance is a
private proof import.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage --uses
AlgebraicGeometry.ProEtale.moduleComplexHigherDirectImage` found one downstream
module, which does not mention the helper or the continuity theorem in its statement.
Its import is private and retained as a proof dependency. No locked target statement
uses this helper; no target meaning changes or target statement re-review is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage | D2 | Same signatures; shared derived construction and proved canonical comparison. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Existing signature and source retained unchanged; checked against the changed dependency. |

## Status

landed 20261018T142043-L-3226495 2026-10-18 (merge of deliver/D2/Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage)
