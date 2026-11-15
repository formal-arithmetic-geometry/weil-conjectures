/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Source-open flat counit presentations

## References

* [Stacks Project](https://stacks.math.columbia.edu), Tags 0A1D, 0DJ9
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- A bounded flat sheaf-complex presentation of the canonical comparison before taking stalks.
This predicate records the base direct-image identification as well
as the ordinary pullback identification, so restriction arrows can be transported
between presentations. It constructs no data by choice. -/
def StandardSingleFlatCounitPresentation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) : Prop :=
  letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI := HasDerivedCategory.standard A.Modules
  letI := HasDerivedCategory.standard B.Modules
  ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
    ∃ (e : (schemeDerivedDirectImage p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))
      (t : DerivedCategory.Qh.obj
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫ t.hom

/-- The presentation property for every relatively flat quasi-coherent module on an open.
No quasi-compactness of the open is built into this predicate; the induction only
asks for it on quasi-compact opens. -/
def StandardSingleFlatCounitOnOpen
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U : Y.Opens) : Prop :=
  ∀ (N : U.toScheme.Modules) [N.IsQuasicoherent],
    N.IsFlatOver (U.ι ≫ p) → StandardSingleFlatCounitPresentation (U.ι ≫ p) N g

end AlgebraicGeometry
