/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtensionData
import WeilConjectures.CategoryTheory.ParametrizedTensorHomSquare
import WeilConjectures.AlgebraicGeometry.EtaleScalarPullbackTensorCoherence

/-! # Geometric naturality of the ordinary coefficient Hom comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso
  AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison
  AlgebraicGeometry.Etale.ExceptionalCoefficients.tensorIso
  AlgebraicGeometry.Etale.scalarPullbackIso
  AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂
  AlgebraicGeometry.Etale.derivedTensorHomAdjunction
  AlgebraicGeometry.Etale.derivedHom
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

private def closedAdjunction₂ (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    derivedTensor (ModuleCat.{u + 1} A) X ⊣₂ derivedHom (ModuleCat.{u + 1} A) X where
  adj K := closed A X K
  unit_whiskerRight_map f := by
    simpa only [closed, derivedTensorHomAdjunction] using
      (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X).unit_whiskerRight_map f


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

private def pullTensor (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) :
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) X) ⋙ Sites.pull A g ≅
      (Sites.pull A g).prod (Sites.pull A g) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) Y) :=
  uncurryTensorIso (Sites.pull A g)
    (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} A) Y)
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) g)


private theorem inverse_three_square
    {C : Type*} [Category C] {X Y Z W V U : C}
    (e : X ⟶ Y) (p : Y ≅ Z) (q : Z ≅ W)
    (r : X ≅ V) (s : V ≅ U) (v : U ⟶ W)
    (h : e ≫ p.hom ≫ q.hom = r.hom ≫ s.hom ≫ v) :
    v ≫ q.inv ≫ p.inv = s.inv ≫ r.inv ≫ e := by
  apply (cancel_epi (r.hom ≫ s.hom)).1
  have hh := congrArg (fun z ↦ z ≫ q.inv ≫ p.inv) h.symm
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh


private theorem pullTensor_inv_app
    (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) (K L : Cat A X) :
    (pullTensor A g).inv.app (K, L) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K L).inv := by
  unfold leftDerivedUpperStarTensorIso
  rfl

private theorem scalar_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) (K L : Cat A X) :
    ((Sites.scalarPull φ g).hom.app K ⊗ₘ (Sites.scalarPull φ g).hom.app L) ≫
        (ExceptionalCoefficients.tensorIso φ Y).inv.app
          ((Sites.pull A g).obj K, (Sites.pull A g).obj L) ≫
        (scalarExtension φ Y).map ((pullTensor A g).inv.app (K, L)) =
      (pullTensor B g).inv.app ((scalarExtension φ X).obj K, (scalarExtension φ X).obj L) ≫
        (Sites.pull B g).map ((ExceptionalCoefficients.tensorIso φ X).inv.app (K, L)) ≫
        (Sites.scalarPull φ g).hom.app (K ⊗ L) := by
  simp only [pullTensor_inv_app]
  exact inverse_three_square
    ((Sites.scalarPull φ g).hom.app (K ⊗ L))
    ((scalarExtension φ Y).mapIso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K L))
    ((ExceptionalCoefficients.tensorIso φ Y).app
      ((Sites.pull A g).obj K, (Sites.pull A g).obj L))
    ((Sites.pull B g).mapIso ((ExceptionalCoefficients.tensorIso φ X).app (K, L)))
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) g
      ((scalarExtension φ X).obj K) ((scalarExtension φ X).obj L))
    ((Sites.scalarPull φ g).hom.app K ⊗ₘ (Sites.scalarPull φ g).hom.app L)
    (etaleScalarPullback_tensor φ g K L)



private theorem transpose_evaluation
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {K : C} {M : D} (f : F.obj K ⟶ M) :
    F.map ((a.homEquiv K M) f) ≫ a.counit.app M = f := by
  exact (a.homEquiv K M).symm_apply_apply f

private theorem homMap_evaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K M : Cat A X) :
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj K)).map
        (homMap φ X K M) ≫
        (closed B X ((scalarExtension φ X).obj K)).counit.app
          ((scalarExtension φ X).obj M) =
      (ExceptionalCoefficients.tensorIso φ X).inv.app
          (K, ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
        (scalarExtension φ X).map ((closed A X K).counit.app M) := by
  dsimp only [homMap, Functor.id_obj, Functor.prod_obj]
  exact transpose_evaluation (closed B X ((scalarExtension φ X).obj K))
    ((ExceptionalCoefficients.tensorIso φ X).inv.app
      (K, ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
      (scalarExtension φ X).map ((closed A X K).counit.app M))


private theorem pullHom_evaluation
    (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (K M : Cat A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((Sites.pull A g).obj K)).map
        (Sites.pullHom A g K M) ≫
        (closed A Y ((Sites.pull A g).obj K)).counit.app ((Sites.pull A g).obj M) =
      (pullTensor A g).inv.app
          (K, ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
        (Sites.pull A g).map ((closed A X K).counit.app M) := by
  rw [pullTensor_inv_app]
  dsimp only [Sites.pullHom, Functor.id_obj]
  exact transpose_evaluation
    (closed A Y ((Sites.pull A g).obj K))
    (M := (Sites.pull A g).obj M)
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).inv ≫
      (Sites.pull A g).map ((closed A X K).counit.app M))


set_option maxHeartbeats 2000000 in
-- The concrete derived comparison types require additional kernel reductions.
/-- Coefficient extension and isomorphism pullback commute on the Hom comparison.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph.
(blueprint: lem-sf-coefficient-map-hom-geometry).
Proof: apply the tensor square for scalar/pullback to K and internalHom(K,M).
Transpose both evaluation comparisons by tensor--Hom. Tensor naturality gives
scalar extension of the pulled-back evaluation on both paths, and naturality of
the scalar/pullback isomorphism at evaluation identifies the remaining maps.
The argument works on all derived objects, so in particular on the stated
finite-Tor constructible domain. It uses no flatness of the coefficient map. -/
theorem coefficient_map_hom_geometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) (X : Scheme.{u}) : Sites.HomGeometry φ X := by
  intro Y e K M _hK _hM
  have h := paramTensorComparisonHom_square_of_evaluation
    (TC := derivedTensor (ModuleCat.{u + 1} A) X)
    (TD := derivedTensor (ModuleCat.{u + 1} B) X)
    (TE := derivedTensor (ModuleCat.{u + 1} A) Y)
    (TJ := derivedTensor (ModuleCat.{u + 1} B) Y)
    (HC := derivedHom (ModuleCat.{u + 1} A) X)
    (HD := derivedHom (ModuleCat.{u + 1} B) X)
    (HE := derivedHom (ModuleCat.{u + 1} A) Y)
    (HJ := derivedHom (ModuleCat.{u + 1} B) Y)
    (closedAdjunction₂ A X)
    (closedAdjunction₂ B X)
    (closedAdjunction₂ A Y)
    (closedAdjunction₂ B Y)
    (scalarExtension φ X) (scalarExtension φ Y)
    (Sites.pull A e.hom) (Sites.pull B e.hom)
    (ExceptionalCoefficients.tensorIso φ X) (ExceptionalCoefficients.tensorIso φ Y)
    (pullTensor A e.hom) (pullTensor B e.hom) (Sites.scalarPull φ e.hom)
    (homMap φ X) (homMap φ Y) (Sites.pullHom A e.hom) (Sites.pullHom B e.hom)
    (homMap_evaluation φ X) (homMap_evaluation φ Y)
    (pullHom_evaluation A e.hom) (pullHom_evaluation B e.hom)
    (by
      intro K' L'
      simpa only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj, derivedTensor,
        curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj,
        MonoidalCategory.tensorHom_def, Functor.comp_obj]
        using scalar_tensor_square φ e.hom K' L') K M
  unfold homAction
  exact h

end WeilConjectures.FiniteFreeCoefficients
