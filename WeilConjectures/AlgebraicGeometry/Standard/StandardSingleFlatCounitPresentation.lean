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

Source: Stacks Project, Tags 0A1D and 0DJ9.
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
Source: Stacks Project, Tags 0A1D and 0DJ9, affine calculation and relative Mayer--Vietoris.
It records both the base direct-image and the pullback identification. -/
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
Source: Stacks Project, Tag 0DJ9, property of source opens used in the induction. -/
def StandardSingleFlatCounitOnOpen
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U : Y.Opens) : Prop :=
  ∀ (N : U.toScheme.Modules) [N.IsQuasicoherent],
    N.IsFlatOver (U.ι ≫ p) → StandardSingleFlatCounitPresentation (U.ι ≫ p) N g

end AlgebraicGeometry
