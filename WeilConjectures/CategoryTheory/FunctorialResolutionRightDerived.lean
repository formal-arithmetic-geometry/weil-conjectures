/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FunctorialNonnegativeInjectiveResolution
public import WeilConjectures.Algebra.Homology.FunctorCategoryHomologyEvaluation

/-! # Functorial resolutions compute right derived functors

Source: Stacks Project, Derived Categories, Tag 015E. Evaluate the explicitly
constructed diagram resolution, compute with that injective resolution, and use
naturality of the injective-resolution comparison.
(blueprint: new-finite-cover-functorial-resolution-derived)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uK vK uA vA w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {K : Type uK} [Category.{vK} K] (D : K ⥤ C)
  {A : Type uA} [Category.{vA} A] [Abelian A] (F : C ⥤ A) [F.Additive]

/-- Apply an additive functor termwise to the chosen diagram resolution.
Source: Stacks Project, Tag 015E.
(blueprint: new-finite-cover-functorial-resolution-derived) -/
def nonnegativeInjectiveImageComplex : CochainComplex (K ⥤ A) ℕ :=
  ((((whiskeringRight K C A).obj F).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    D.nonnegativeInjectiveComplex)

/-- The image complex computes the right derived functor, naturally in the diagram variable.
Source: Stacks Project, Tag 015E. The evaluated augmentation is an injective resolution.
The resolution augmentation is natural, so the standard comparison with the right derived
functor is natural. Evaluation commutes with homology.
(blueprint: new-finite-cover-functorial-resolution-derived) -/
def nonnegativeInjectiveImageHomologyIso (q : ℕ) :
    (D.nonnegativeInjectiveImageComplex F).homology q ≅ D ⋙ F.rightDerived q :=
  ((D.nonnegativeInjectiveImageComplex F).homologyAsFunctorIso q).symm ≪≫
    NatIso.ofComponents (fun x ↦
      ((D.nonnegativeInjectiveResolution x).isoRightDerivedObj F q).symm)
      (fun {x y} g ↦ by
        have hcomm : (D.nonnegativeInjectiveResolution x).ι.f 0 ≫
            (D.nonnegativeInjectiveComplex.asFunctor.map g).f 0 =
          D.map g ≫ (D.nonnegativeInjectiveResolution y).ι.f 0 := by
          simpa [nonnegativeInjectiveResolution, mapResolution] using
            (D.nonnegativeInjectiveAugmentation.f 0).naturality g
        exact (InjectiveResolution.isoRightDerivedObj_inv_naturality (D.map g)
          (D.nonnegativeInjectiveResolution x) (D.nonnegativeInjectiveResolution y)
          (D.nonnegativeInjectiveComplex.asFunctor.map g) hcomm F q).symm)

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {K : Type uK} [Category.{vK} K] (D : K ⥤ C)
  {A : Type uA} [Category.{vA} A] [Abelian A]
  {F G : C ⥤ A} [F.Additive] [G.Additive]

/-- A transformation of additive functors acts termwise on the resolved image complex.
Source: Stacks Project, Tag 015E.
(blueprint: new-finite-cover-functorial-resolution-derived) -/
def nonnegativeInjectiveImageMap (α : F ⟶ G) :
    D.nonnegativeInjectiveImageComplex F ⟶ D.nonnegativeInjectiveImageComplex G where
  f n := whiskerLeft (D.nonnegativeInjectiveComplex.X n) α
  comm' i j _ := by
    ext x
    exact (α.naturality ((D.nonnegativeInjectiveComplex.d i j).app x)).symm

/-- The derived comparison respects transformations of the functor being derived.
Source: Stacks Project, Tag 015E. Evaluate at an object and use the standard formula
for a derived natural transformation computed on an injective resolution; naturality
of the evaluation-homology comparison transports this equality to the functor category.
(blueprint: new-finite-cover-functorial-resolution-derived) -/
theorem nonnegativeInjectiveImageHomologyIso_naturality (α : F ⟶ G) (q : ℕ) :
    HomologicalComplex.homologyMap (D.nonnegativeInjectiveImageMap α) q ≫
        (D.nonnegativeInjectiveImageHomologyIso G q).hom =
      (D.nonnegativeInjectiveImageHomologyIso F q).hom ≫
        whiskerLeft D (NatTrans.rightDerived α q) := by
  ext x
  let I := D.nonnegativeInjectiveResolution x
  let eF := (D.nonnegativeInjectiveImageComplex F).homologyEvaluationIso q x
  let eG := (D.nonnegativeInjectiveImageComplex G).homologyEvaluationIso q x
  have he := (D.nonnegativeInjectiveImageComplex F).homologyEvaluationIso_hom_naturality
    (D.nonnegativeInjectiveImageMap α) q x
  dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex] at he
  change (HomologicalComplex.homologyMap (D.nonnegativeInjectiveImageMap α) q).app x ≫
      (eG.inv ≫ (I.isoRightDerivedObj G q).inv) =
    (eF.inv ≫ (I.isoRightDerivedObj F q).inv) ≫ (NatTrans.rightDerived α q).app (D.obj x)
  rw [← cancel_epi eF.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Category.assoc, ← he]
  dsimp only [eG]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [InjectiveResolution.rightDerived_app_eq α I q]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- The same comparison for a resolution of the identity functor, with its left
unitor included. Source: Stacks Project, Tag 015E; naturality of the left unitor
applied to the preceding comparison.
(blueprint: new-finite-cover-functorial-resolution-derived) -/
theorem identity_nonnegativeInjectiveImageHomologyIso_naturality (α : F ⟶ G) (q : ℕ) :
    HomologicalComplex.homologyMap ((𝟭 C).nonnegativeInjectiveImageMap α) q ≫
        ((𝟭 C).nonnegativeInjectiveImageHomologyIso G q ≪≫ Functor.leftUnitor _).hom =
      ((𝟭 C).nonnegativeInjectiveImageHomologyIso F q ≪≫ Functor.leftUnitor _).hom ≫
        NatTrans.rightDerived α q := by
  have hu : whiskerLeft (𝟭 C) (NatTrans.rightDerived α q) ≫
      (Functor.leftUnitor (G.rightDerived q)).hom =
        (Functor.leftUnitor (F.rightDerived q)).hom ≫ NatTrans.rightDerived α q := by
    apply NatTrans.ext
    funext x
    change (NatTrans.rightDerived α q).app x ≫ 𝟙 _ =
      𝟙 _ ≫ (NatTrans.rightDerived α q).app x
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  simp only [Iso.trans_hom]
  rw [← Category.assoc, nonnegativeInjectiveImageHomologyIso_naturality]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ ((𝟭 C).nonnegativeInjectiveImageHomologyIso F q).hom ≫ z) hu

end CategoryTheory.Functor
