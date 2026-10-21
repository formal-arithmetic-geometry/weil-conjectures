/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct

/-! # Naturality of the actual pro-etale supported exterior product

Source: blueprint `lem-pur-kunneth-supported`, witness-transport paragraph.
(blueprint: lem-pur-proetale-supported-product-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] HomologicalComplex₂.total
set_option backward.isDefEq.respectTransparency true
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale

open Lean Lean.Meta Lean.Elab.Tactic in
private meta def supportedStructureCongr : Nat → MVarId → TacticM Unit
  | 0, _ => throwError "structural congruence exhausted"
  | fuel + 1, g => g.withContext do
      let ty ← instantiateMVars (← g.getType)
      if let some _ := ty.eq? then
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``eq_of_heq)
        for g' in gs do supportedStructureCongr fuel g'
      else if let some (_, lhs, _, rhs) := ty.heq? then
        if lhs == rhs || (← isProof lhs) then
          g.assign (← mkHEqRefl lhs)
        else
          let f := lhs.getAppFn
          if (← isDefEq f rhs.getAppFn) && lhs.getAppNumArgs == rhs.getAppNumArgs then
            let h ← mkHCongrWithArity f lhs.getAppNumArgs
            let gs ← g.apply h.proof { synthAssignedInstances := false }
            for g' in gs do supportedStructureCongr fuel g'
          else
            unless ← isDefEq lhs rhs do
              throwError "structural congruence: different heads {f} / {rhs.getAppFn}"
            g.assign (← mkHEqRefl lhs)
      else
        g.assign (← synthInstance ty)


private theorem evaluation_natural
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : D ⥤ C) (G G' : D ⥤ E) (H : C ⥤ E)
    (σ : H ≅ F ⋙ G) (ε : R ⋙ F ⟶ 𝟭 D) (τ : G' ≅ G)
    {K K' : D} (a : K ⟶ K') :
    H.map (R.map a) ≫
        (σ.hom.app (R.obj K') ≫ G.map (ε.app K') ≫ τ.inv.app K') =
      (σ.hom.app (R.obj K) ≫ G.map (ε.app K) ≫ τ.inv.app K) ≫ G'.map a := by
  exact (Functor.whiskerLeft R σ.hom ≫ Functor.whiskerRight ε G ≫ τ.inv).naturality a

private def bifunctorMap {D : Type*} [Category D] (T : D ⥤ D ⥤ D)
    {U U' V V' : D} (a : U ⟶ U') (b : V ⟶ V') :
    (T.obj U).obj V ⟶ (T.obj U').obj V' :=
  (T.map a).app V ≫ (T.obj U').map b

private theorem bifunctorMap_comp {D : Type*} [Category D] (T : D ⥤ D ⥤ D)
    {U U' U'' V V' V'' : D} (a : U ⟶ U') (b : V ⟶ V')
    (a' : U' ⟶ U'') (b' : V' ⟶ V'') :
    bifunctorMap T a b ≫ bifunctorMap T a' b' = bifunctorMap T (a ≫ a') (b ≫ b') := by
  simp only [bifunctorMap, Category.assoc, Functor.map_comp, NatTrans.comp_app]
  rw [(T.map a').naturality_assoc b]

private theorem adjunct_bifunctor_pairing_natural
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R) (T : D ⥤ D ⥤ D)
    {M M' N N' : C} {U U' V V' P P' Q Q' : D}
    (a : M ⟶ M') (b : N ⟶ N') (x : U ⟶ U') (y : V ⟶ V')
    (t : F.obj (M ⊗ N) ⟶ (T.obj U).obj V)
    (t' : F.obj (M' ⊗ N') ⟶ (T.obj U').obj V')
    (v : U ⟶ P) (v' : U' ⟶ P') (w : V ⟶ Q) (w' : V' ⟶ Q')
    (p : P ⟶ P') (q : Q ⟶ Q')
    (ht : F.map (a ⊗ₘ b) ≫ t' = t ≫ bifunctorMap T x y)
    (hv : x ≫ v' = v ≫ p) (hw : y ≫ w' = w ≫ q) :
    (a ⊗ₘ b) ≫ adj.homEquiv _ _ (t' ≫ bifunctorMap T v' w') =
      adj.homEquiv _ _ (t ≫ bifunctorMap T v w) ≫ R.map (bifunctorMap T p q) := by
  apply adj.homEquiv_naturality_left_square
  rw [← Category.assoc, ht, Category.assoc, bifunctorMap_comp, hv, hw,
    ← bifunctorMap_comp, ← Category.assoc]

private theorem castFamily_natural
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (G F₁ F₂ : C ⥤ D) (T : D ⥤ D ⥤ D) (hT : T = curriedTensor D)
    (e : (∀ M N : C, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N) =
      (∀ M N : C, G.obj (M ⊗ N) ⟶ (T.obj (F₁.obj M)).obj (F₂.obj N)))
    (t : ∀ M N : C, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N)
    (ht : ∀ (M M' N N' : C) (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ (F₁.map a ⊗ₘ F₂.map b))
    {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N') :
    G.map (a ⊗ₘ b) ≫ (cast e t) M' N' = (cast e t) M N ≫
      bifunctorMap T (F₁.map a) (F₂.map b) := by
  subst T
  simpa only [cast_eq, bifunctorMap, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using ht M M' N N' a b

private theorem tensorFunctor_eq_generic
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) :
    derivedTensor C T = curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :=
  rfl

private theorem tensorFunctor_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    derivedTensor (ModuleCat.{u + 1} A) T =
      curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) := by
  refine Eq.mp ?_ (tensorFunctor_eq_generic (ModuleCat.{u + 1} A) T)
  run_tac do
    for g in ← Lean.Elab.Tactic.getGoals do supportedStructureCongr 40 g
    Lean.Elab.Tactic.setGoals []

private theorem comparison_cast_natural
    {C D : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (θ : ∀ P Q : CochainComplex C ℤ, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (ht : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ θ t)
    (T : DerivedCategory D ⥤ DerivedCategory D ⥤ DerivedCategory D)
    (hT : T = curriedTensor (DerivedCategory D))
    (e : SupportedTensorDerivation.ComparisonHom G F₁ F₂ =
      (∀ M N : DerivedCategory C, G.mapDerivedCategory.obj (M ⊗ N) ⟶
        (T.obj (F₁.mapDerivedCategory.obj M)).obj (F₂.mapDerivedCategory.obj N)))
    {M M' N N' : DerivedCategory C} (a : M ⟶ M') (b : N ⟶ N') :
    G.mapDerivedCategory.map (a ⊗ₘ b) ≫ (cast e t) M' N' =
      (cast e t) M N ≫ bifunctorMap T
        (F₁.mapDerivedCategory.map a) (F₂.mapDerivedCategory.map b) := by
  refine castFamily_natural G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
    T hT e t ?_ a b
  intro M M' N N' a b
  simpa only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
    curriedTensor_obj_map, Category.assoc] using ht.1 M M' N N' a b

private theorem comparison_natural (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    {M M' N N' : DerivedCategory (ModuleCat.{u + 1} A)} (a : M ⟶ M') (b : N ⟶ N') :
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.map
        (a ⊗ₘ b) ≫ supportedCoefficientTensorDerived A f g i j M' N' =
      supportedCoefficientTensorDerived A f g i j M N ≫
        supportedDerivedTensorMap A (pullback f g)
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.map a)
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.map b) := by
  exact comparison_cast_natural
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorComplex A f g i j)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose_spec.1
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (tensorFunctor_eq A (pullback f g))
    (supportedCoefficientTensorDerivedHom_tensor A f g i j) a b

private theorem adjunct_pairing_isIso_of_iso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R) (T : D ⥤ D ⥤ D)
    {M M' N N' : C} {U U' V V' P P' Q Q' : D}
    (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b]
    (x : U ⟶ U') (y : V ⟶ V')
    (t : F.obj (M ⊗ N) ⟶ (T.obj U).obj V)
    (t' : F.obj (M' ⊗ N') ⟶ (T.obj U').obj V')
    (v : U ⟶ P) (v' : U' ⟶ P') (w : V ⟶ Q) (w' : V' ⟶ Q')
    (p : P ⟶ P') (q : Q ⟶ Q') [IsIso p] [IsIso q]
    (ht : F.map (a ⊗ₘ b) ≫ t' = t ≫ bifunctorMap T x y)
    (hv : x ≫ v' = v ≫ p) (hw : y ≫ w' = w ≫ q)
    (hκ : IsIso (adj.homEquiv _ _ (t ≫ bifunctorMap T v w))) :
    IsIso (adj.homEquiv _ _ (t' ≫ bifunctorMap T v' w')) := by
  have hn := adjunct_bifunctor_pairing_natural adj T a b x y t t' v v' w w' p q ht hv hw
  have := hκ
  have : IsIso (bifunctorMap T p q) := by unfold bifunctorMap; infer_instance
  have : IsIso ((a ⊗ₘ b) ≫ adj.homEquiv _ _ (t' ≫ bifunctorMap T v' w')) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (a ⊗ₘ b)
    (adj.homEquiv _ _ (t' ≫ bifunctorMap T v' w'))

private theorem firstEvaluation_natural (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] [IsLocallyNoetherian X]
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : K ⟶ K') :
    (supportedFirstCoefficients A f g b).mapDerivedCategory.map
        ((supportedSectionsDerived A b).map a) ≫ supportedFirstEvaluation A f g b K' =
      supportedFirstEvaluation A f g b K ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map a := by
  exact evaluation_natural (supportedCoefficients A b).mapDerivedCategory
    (supportedSectionsDerived A b)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor
    (supportedFirstCoefficients A f g b).mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)))
    (supportedCoefficientDerivedAdjunction A b).counit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (pullback.fst f g)) a

private theorem secondEvaluation_natural (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] [IsLocallyNoetherian Y]
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (e : L ⟶ L') :
    (supportedSecondCoefficients A f g d).mapDerivedCategory.map
        ((supportedSectionsDerived A d).map e) ≫ supportedSecondEvaluation A f g d L' =
      supportedSecondEvaluation A f g d L ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map e := by
  exact evaluation_natural (supportedCoefficients A d).mapDerivedCategory
    (supportedSectionsDerived A d)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor
    (supportedSecondCoefficients A f g d).mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)))
    (supportedCoefficientDerivedAdjunction A d).counit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (pullback.snd f g)) e

/-- Invertibility of the actual pairing is unchanged by specified isomorphisms of
its coefficient objects. Source: blueprint witness-transport paragraph
(blueprint: lem-pur-proetale-supported-product-naturality).

Proof: naturality of the derived coefficient comparison and of the two evaluation
counits gives a commutative square of their tensor composites. Transposing the square
under the normalized coefficient adjunction gives the square for supported sections.
Its vertical arrows are the tensor of the supported-section images of the given
isomorphisms and the supported-section image of their external tensor. All are
isomorphisms. Cancel them to transfer invertibility. The final definitional transport
from the explicit tensor presentation to the external product is also an isomorphism.
-/
theorem isIso_supportedExteriorProduct_of_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (eK : K ≅ K') (eL : L ≅ L')
    (hκ : IsIso (supportedExteriorProduct A f g i j K L)) :
    IsIso (supportedExteriorProduct A f g i j K' L') := by
  unfold supportedExteriorProduct at hκ ⊢
  have := hκ
  have hraw : IsIso
      ((supportedCoefficientDerivedAdjunction A
        (Etale.supportedProductImmersion f g i j)).homEquiv _ _
        (supportedCoefficientTensorDerived A f g i j
            ((supportedSectionsDerived A i).obj K) ((supportedSectionsDerived A j).obj L) ≫
          supportedDerivedTensorMap A (pullback f g)
            (supportedFirstEvaluation A f g i K) (supportedSecondEvaluation A f g j L))) := by
    exact IsIso.of_isIso_comp_right _
      ((supportedSectionsDerived A (Etale.supportedProductImmersion f g i j)).map
        (eqToHom (supportedExternalProduct_eq A f g K L)))
  apply IsIso.comp_isIso'
  · exact adjunct_pairing_isIso_of_iso
      (supportedCoefficientDerivedAdjunction A (Etale.supportedProductImmersion f g i j))
      (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
      ((supportedSectionsDerived A i).map eK.hom)
      ((supportedSectionsDerived A j).map eL.hom)
      _ _ _ _ _ _ _ _ _ _
      (comparison_natural A f g i j _ _)
      (firstEvaluation_natural A f g i eK.hom) (secondEvaluation_natural A f g j eL.hom) hraw
  · infer_instance

end AlgebraicGeometry.ProEtale
