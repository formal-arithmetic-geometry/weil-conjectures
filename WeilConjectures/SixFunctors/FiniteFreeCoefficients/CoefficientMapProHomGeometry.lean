/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.CategoryTheory.SixFunctors.ParametrizedTensorHomSquare

/-! # Geometric naturality of the pro-etale coefficient Hom comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients


private def uncurryTensorComparison
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) :
    Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj S where
  app Z := (t.app Z.1).app Z.2
  naturality X Y f := by
    have h := (Functor.uncurry.map t).naturality f
    change (F.map ((T.map f.1).app X.2) ≫
      F.map ((T.obj Y.1).map f.2)) ≫ (t.app Y.1).app Y.2 = _ at h
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ = _
    rw [F.map_comp]
    exact h


private def proAdjunction₂ (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Sites.tensor true A X ⊣₂ Sites.hom true A X where
  adj K := Sites.adj true A X K
  unit_whiskerRight_map f := by
    simpa only [Sites.adj, Sites.tensor, Sites.hom, _root_.id,
      ProEtale.derivedTensorHomAdjunction] using
      (ProEtale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X).unit_whiskerRight_map f


private def uncurryTensorIso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (e : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj S :=
  NatIso.ofComponents (fun KL ↦ (e.app KL.1).app KL.2)
    (by
      intro X Y f
      exact (uncurryTensorComparison F T S e.hom).naturality f)

private def proPullTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) :
    Functor.uncurry.obj (Sites.tensor true A X) ⋙ Sites.proPull A g ≅
      (Sites.proPull A g).prod (Sites.proPull A g) ⋙
        Functor.uncurry.obj (Sites.tensor true A Y) :=
  uncurryTensorIso (Sites.proPull A g)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y)
    (ProEtale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) g)


private theorem proPullTensor_inv_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) (K L : Sites.D true A X) :
    (proPullTensor A g).inv.app (K, L) =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K L).inv := by
  unfold ProEtale.leftDerivedUpperStarTensorIso
  rfl

attribute [local irreducible] Sites.adj

private theorem transpose_evaluation
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {K : C} {M : D} (f : F.obj K ⟶ M) :
    F.map ((a.homEquiv K M) f) ≫ a.counit.app M = f := by
  exact (a.homEquiv K M).symm_apply_apply f

private theorem proHomMap_evaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (K M : Sites.D true A X) :
    ((Sites.tensor true B X).obj ((Sites.scalar true φ X).obj K)).map
        (Sites.homMap true φ X μ K M) ≫
        (Sites.adj true B X ((Sites.scalar true φ X).obj K)).counit.app
          ((Sites.scalar true φ X).obj M) =
      μ.inv.app (K, ((Sites.hom true A X).obj (op K)).obj M) ≫
        (Sites.scalar true φ X).map ((Sites.adj true A X K).counit.app M) := by
  dsimp only [Sites.homMap, Functor.id_obj, Functor.prod_obj]
  exact transpose_evaluation (Sites.adj true B X ((Sites.scalar true φ X).obj K))
    (μ.inv.app (K, ((Sites.hom true A X).obj (op K)).obj M) ≫
      (Sites.scalar true φ X).map ((Sites.adj true A X K).counit.app M))


private theorem proPullHom_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) (K M : Sites.D true A X) :
    ((Sites.tensor true A Y).obj ((Sites.proPull A g).obj K)).map
        (Sites.proPullHom A g K M) ≫
        (Sites.adj true A Y ((Sites.proPull A g).obj K)).counit.app
          ((Sites.proPull A g).obj M) =
      (proPullTensor A g).inv.app (K, ((Sites.hom true A X).obj (op K)).obj M) ≫
        (Sites.proPull A g).map ((Sites.adj true A X K).counit.app M) := by
  rw [proPullTensor_inv_app]
  dsimp only [Sites.proPullHom, Functor.id_obj]
  exact transpose_evaluation
    (Sites.adj true A Y ((Sites.proPull A g).obj K))
    (M := (Sites.proPull A g).obj M)
    ((ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
      (((Sites.hom true A X).obj (op K)).obj M)).inv ≫
      (Sites.proPull A g).map ((Sites.adj true A X K).counit.app M))


set_option maxHeartbeats 2000000 in
-- The concrete derived comparison types require additional kernel reductions.
/-- A scalar/pullback tensor square gives its evaluation-defined pro-etale Hom square.
Source: blueprint latest, coefficient extension proof, final paragraph.
(blueprint: lem-sf-coefficient-pro-hom-geometry-of-tensor).
Proof: use the tensor square at K and [K,M]. Transpose both composites by the
actual tensor--Hom adjunction. Naturality of both tensor comparisons and of the
scalar/pullback isomorphism at evaluation identifies the transposes. -/
theorem coefficient_map_pro_hom_geometry_of_tensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (ht : ∀ (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y),
      Sites.NormalizedTensor true φ Y δ → ∀ K L : Sites.D true A X,
      ((Sites.proScalarPull φ e.hom).hom.app K ⊗ₘ
        (Sites.proScalarPull φ e.hom).hom.app L) ≫
        δ.inv.app ((Sites.proPull A e.hom).obj K, (Sites.proPull A e.hom).obj L) ≫
        (Sites.scalar true φ Y).map
          (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e.hom K L).inv =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom
        ((Sites.scalar true φ X).obj K) ((Sites.scalar true φ X).obj L)).inv ≫
        (Sites.proPull B e.hom).map (μ.inv.app (K, L)) ≫
        (Sites.proScalarPull φ e.hom).hom.app (K ⊗ L)) :
    Sites.ProHomGeometry φ X μ := by
  intro Y e δ hδ K M _hK _hM
  have h := paramTensorComparisonHom_square_of_evaluation
    (TC := Sites.tensor true A X) (TD := Sites.tensor true B X)
    (TE := Sites.tensor true A Y) (TJ := Sites.tensor true B Y)
    (HC := Sites.hom true A X) (HD := Sites.hom true B X)
    (HE := Sites.hom true A Y) (HJ := Sites.hom true B Y)
    (proAdjunction₂ A X) (proAdjunction₂ B X)
    (proAdjunction₂ A Y) (proAdjunction₂ B Y)
    (Sites.scalar true φ X) (Sites.scalar true φ Y)
    (Sites.proPull A e.hom) (Sites.proPull B e.hom) μ δ
    (proPullTensor A e.hom) (proPullTensor B e.hom) (Sites.proScalarPull φ e.hom)
    (Sites.homMap true φ X μ) (Sites.homMap true φ Y δ)
    (Sites.proPullHom A e.hom) (Sites.proPullHom B e.hom)
    (proHomMap_evaluation φ X μ) (proHomMap_evaluation φ Y δ)
    (proPullHom_evaluation A e.hom) (proPullHom_evaluation B e.hom)
    (by
      intro K' L'
      rw [proPullTensor_inv_app, proPullTensor_inv_app]
      simpa only [Sites.tensor, _root_.id, Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
        ProEtale.derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
        curriedTensor_obj_obj, MonoidalCategory.tensorHom_def, Functor.comp_obj,
        Sites.proPull]
        using ht Y e δ hδ K' L') K M
  unfold homAction
  exact h

end WeilConjectures.FiniteFreeCoefficients
