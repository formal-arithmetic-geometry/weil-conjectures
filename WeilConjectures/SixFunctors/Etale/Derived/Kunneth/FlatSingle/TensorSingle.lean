/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-!
# The comparison between derived and underived tensor products of sheaves

For sheaves `A`, `B` on the small étale site of `X`, placed in degree `0`, there is a natural
morphism `A[0] ⊗ᴸ B[0] ⟶ (A ⊗ B)[0]` (`AlgebraicGeometry.Etale.singleFunctorTensorToSingle`),
natural in `A`, obtained from the lax monoidal structure of `Qh : K(X_ét) ⥤ D(X_ét)`. It is an
isomorphism for `A` flat (compare `AlgebraicGeometry.Etale.singleFunctorObjTensorIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The lax monoidal structure `Qh K ⊗ Qh L ⟶ Qh (K ⊗ L)` of the localization functor
`Qh : K(X_ét) ⥤ D(X_ét)`, as a natural transformation in `K` for a fixed `L`. -/
@[simps]
noncomputable def qhTensorRightμ (L : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    DerivedCategory.Qh ⋙ tensorRight (DerivedCategory.Qh.obj L) ⟶
      tensorRight L ⋙ DerivedCategory.Qh where
  app K := Functor.LaxMonoidal.μ DerivedCategory.Qh K L
  naturality K K' f := by
    dsimp
    exact Functor.LaxMonoidal.μ_natural_left _ _ _

/-- The monoidal structure of the quotient functor `C(X_ét) ⥤ K(X_ét)`, as a natural isomorphism
in the first variable. -/
noncomputable def quotientTensorRightIso (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    HomotopyCategory.quotient _ (.up ℤ) ⋙
        tensorRight ((HomotopyCategory.quotient _ (.up ℤ)).obj L) ≅
      tensorRight L ⋙ HomotopyCategory.quotient _ (.up ℤ) :=
  NatIso.ofComponents (fun K ↦ Functor.Monoidal.μIso (HomotopyCategory.quotient _ (.up ℤ)) K L)
    (fun f ↦ by
      dsimp
      rw [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_hom]
      exact Functor.LaxMonoidal.μ_natural_left _ _ _)

variable (A X) in
/-- The functor `A ↦ A[0]` to the derived category, as the composite through the homotopy
category. -/
noncomputable def singleFunctorIsoQh :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ≅
      HomologicalComplex.single _ (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (.up ℤ) ⋙
        DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQ _ 0 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm

/-- On single complexes, tensoring with `B[0]` is the termwise tensor product with `B`. -/
noncomputable def singleTensorRightSingleIso (B : Sheaf X.smallEtaleTopology A) :
    HomologicalComplex.single _ (.up ℤ) 0 ⋙
        tensorRight ((HomologicalComplex.single _ (.up ℤ) 0).obj B) ≅
      tensorRight B ⋙ HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0 :=
  Functor.isoWhiskerLeft (HomologicalComplex.single _ (.up ℤ) 0)
      (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _) B) ≪≫
    HomologicalComplex.singleMapHomologicalComplex (tensorRight B) (.up ℤ) 0

/-- The comparison `A[0] ⊗ᴸ B[0] ⟶ (A ⊗ B)[0]` between the derived and the underived tensor
products of sheaves placed in degree `0`, as a natural transformation in `A`. -/
noncomputable def singleFunctorTensorToSingle (B : Sheaf X.smallEtaleTopology A) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ⟶
      tensorRight B ⋙ DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 :=
  let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0
  let qt := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)
  let a₁ : DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj B) ≅
      (sg ⋙ qt ⋙ DerivedCategory.Qh) ⋙ tensorRight (DerivedCategory.Qh.obj (qt.obj (sg.obj B))) :=
    Functor.isoWhiskerRight (singleFunctorIsoQh A X) _ ≪≫
      Functor.isoWhiskerLeft _ ((tensoringRight _).mapIso ((singleFunctorIsoQh A X).app B))
  let a₂ : (sg ⋙ qt ⋙ DerivedCategory.Qh) ⋙
        tensorRight (DerivedCategory.Qh.obj (qt.obj (sg.obj B))) ⟶
      (sg ⋙ qt) ⋙ tensorRight (qt.obj (sg.obj B)) ⋙ DerivedCategory.Qh :=
    Functor.whiskerLeft (sg ⋙ qt) (qhTensorRightμ (qt.obj (sg.obj B)))
  let a₃ : (sg ⋙ qt) ⋙ tensorRight (qt.obj (sg.obj B)) ⋙ DerivedCategory.Qh ⟶
      ((sg ⋙ tensorRight (sg.obj B)) ⋙ qt) ⋙ DerivedCategory.Qh :=
    Functor.whiskerRight (Functor.whiskerLeft sg (quotientTensorRightIso (sg.obj B)).hom)
      DerivedCategory.Qh
  let a₄ : ((sg ⋙ tensorRight (sg.obj B)) ⋙ qt) ⋙ DerivedCategory.Qh ⟶
      ((tensorRight B ⋙ sg) ⋙ qt) ⋙ DerivedCategory.Qh :=
    Functor.whiskerRight (Functor.whiskerRight (singleTensorRightSingleIso B).hom qt)
      DerivedCategory.Qh
  let a₅ : ((tensorRight B ⋙ sg) ⋙ qt) ⋙ DerivedCategory.Qh ⟶
      tensorRight B ⋙ DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 :=
    Functor.whiskerLeft (tensorRight B) (singleFunctorIsoQh A X).inv
  a₁.hom ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅

/-- The comparison `A[0] ⊗ᴸ B[0] ⟶ (A ⊗ B)[0]` is an isomorphism for `A` flat. -/
lemma isIso_singleFunctorTensorToSingle_app (B : Sheaf X.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (hF : ObjectProperty.flat F) :
    IsIso ((singleFunctorTensorToSingle B).app F) := by
  have hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
        ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj F)) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 hF)
  have h := isIso_μNatTrans_Qh_app_app_of_kFlat_left _
    ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)).obj
      ((HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0).obj B)) hK
  simp only [Functor.LaxMonoidal.μNatTrans_app_app] at h
  dsimp [singleFunctorTensorToSingle]
  rw [qhTensorRightμ_app]
  infer_instance

end Etale

end AlgebraicGeometry
