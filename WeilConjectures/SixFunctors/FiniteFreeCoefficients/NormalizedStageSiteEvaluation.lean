/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData

/-! # Evaluation dinaturality on the two small sites

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.derivedTensor AlgebraicGeometry.Etale.derivedHom
  AlgebraicGeometry.ProEtale.derivedTensor AlgebraicGeometry.ProEtale.derivedHom
  AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂
  AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂
  _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.commShift₂CurriedTensor

-- Keep the derived functors abstract while identifying their site presentations.
universe v₁ w₁

private theorem parametrized_evaluation
    {A : Type v₁} [CategoryTheory.Category.{w₁} A]
    (T : A ⥤ A ⥤ A) (H : Aᵒᵖ ⥤ A ⥤ A) (a : T ⊣₂ H)
    (K K' M : A) (g : K' ⟶ K) :
    (Functor.uncurry.obj T).map
        (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj H).map (Prod.mkHom g.op (𝟙 M)))) ≫
          (a.adj K').counit.app M =
      (Functor.uncurry.obj T).map (Prod.mkHom g (𝟙 _)) ≫ (a.adj K).counit.app M := by
  simpa only [Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] using
      (NatTrans.congr_app (ParametrizedAdjunction.whiskerLeft_map_counit a g) M).symm

/-- The same identity for a unary family that is pointwise the parametrized adjunction. -/
private theorem parametrized_evaluation_of_eq
    {A : Type v₁} [CategoryTheory.Category.{w₁} A]
    (T : A ⥤ A ⥤ A) (H : Aᵒᵖ ⥤ A ⥤ A) (a : T ⊣₂ H)
    (adj : ∀ K : A, T.obj K ⊣ H.obj (op K)) (hadj : ∀ K : A, adj K = a.adj K)
    (K K' M : A) (g : K' ⟶ K) :
    (Functor.uncurry.obj T).map
        (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj H).map (Prod.mkHom g.op (𝟙 M)))) ≫
          (adj K').counit.app M =
      (Functor.uncurry.obj T).map (Prod.mkHom g (𝟙 _)) ≫ (adj K).counit.app M := by
  rw [hadj, hadj]
  exact parametrized_evaluation T H a K K' M g

private theorem etale_evaluation
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K K' M : Sites.D false A X) (g : K' ⟶ K) :
    (Functor.uncurry.obj (Sites.tensor false A X)).map
        (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj (Sites.hom false A X)).map
          (Prod.mkHom g.op (𝟙 M)))) ≫ (Sites.adj false A X K').counit.app M =
      (Functor.uncurry.obj (Sites.tensor false A X)).map
        (Prod.mkHom g (𝟙 _)) ≫ (Sites.adj false A X K).counit.app M :=
  parametrized_evaluation_of_eq (Sites.tensor false A X) (Sites.hom false A X)
    (Etale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X) (Sites.adj false A X)
    (fun _ ↦ rfl) K K' M g

private theorem proetale_evaluation
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K K' M : Sites.D true A X) (g : K' ⟶ K) :
    (Functor.uncurry.obj (Sites.tensor true A X)).map
        (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj (Sites.hom true A X)).map
          (Prod.mkHom g.op (𝟙 M)))) ≫ (Sites.adj true A X K').counit.app M =
      (Functor.uncurry.obj (Sites.tensor true A X)).map
        (Prod.mkHom g (𝟙 _)) ≫ (Sites.adj true A X K).counit.app M :=
  parametrized_evaluation_of_eq (Sites.tensor true A X) (Sites.hom true A X)
    (ProEtale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X) (Sites.adj true A X)
    (fun _ ↦ rfl) K K' M g

/-- Evaluation is dinatural in its first input for the published two-site adjunctions.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, the evaluation
transpose defining the Hom comparison.
(blueprint: lem-sf-normalized-stage-site-evaluation).

Proof: for an arbitrary parametrized adjunction, evaluate its whiskerLeft_map_counit
identity at the output object. Uncurry the two bifunctor maps, remove their identity
components and take the symmetric equation. On each site the chosen Sites.adj is
the unary projection of the published derivedTensorHomAdjunction₂. Split the site
Boolean and apply that generic identity to the corresponding derived adjunction.
This proves the equation for the specified evaluation, with no ctf assumptions. -/
theorem normalized_stage_site_evaluation_dinaturality
    (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K K' M : Sites.D pro A X) (g : K' ⟶ K) :
    (Functor.uncurry.obj (Sites.tensor pro A X)).map
        (Prod.mkHom (𝟙 K') ((Functor.uncurry.obj (Sites.hom pro A X)).map
          (Prod.mkHom g.op (𝟙 M)))) ≫ (Sites.adj pro A X K').counit.app M =
      (Functor.uncurry.obj (Sites.tensor pro A X)).map
        (Prod.mkHom g (𝟙 _)) ≫ (Sites.adj pro A X K).counit.app M := by
  cases pro
  · exact etale_evaluation A X K K' M g
  · exact proetale_evaluation A X K K' M g

end WeilConjectures.FiniteFreeCoefficients
