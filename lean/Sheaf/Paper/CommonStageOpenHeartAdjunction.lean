/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import Sheaf.Paper.ConstructiblePullbackTExact

import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.IntegralSupportFunctorNormalization
import Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms
import Mathlib.CategoryTheory.Adjunction.Restrict
import Sheaf.Paper.SfIntegralPullbackLinearAdjunction
import Mathlib.LinearAlgebra.TensorProduct.Map
import all Sheaf.Paper.IntegralCompactSupportCoefficientData
import Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility
import all Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.AutomorphismConstructibleStageEquivalence
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact extension by zero on the common-stage constructible heart

Source: SGA 4, XVII, §5; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-zl-common-stage-open-heart-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures



-- Keep residue fields abstract during instance matching on different schemes.
attribute [local irreducible] Scheme.residueField

attribute [local irreducible] CategoryTheory.ScalarLocalization.composition

open TensorProduct

namespace Rationalization
open CategoryTheory.ScalarLocalization
variable (R : Type*) [CommRing R] (p : R)
  {C : Type*} [Category C] [Preadditive C] [Linear R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def liftLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} := (F.mapLinearMap R).baseChange (Localization.Away p)
  map_id X := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (1 ⊗ₜ[R] 𝟙 X.obj) = _
    rw [LinearMap.baseChange_tmul]
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 X.obj) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj X.obj)
    rw [F.map_id]
  map_comp {X Y Z} f g := by
    change (F.mapLinearMap R).baseChange (Localization.Away p)
      (composition R C p X.obj Y.obj Z.obj g f) =
      composition R D p _ _ _
        ((F.mapLinearMap R).baseChange (Localization.Away p) g)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    induction g using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul b g =>
      induction f using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a f =>
        simp only [composition_tmul, LinearMap.baseChange_tmul,
          CategoryTheory.Functor.coe_mapLinearMap]
        change (b * a) ⊗ₜ[R] F.map (f ≫ g) =
          (b * a) ⊗ₜ[R] (F.map f ≫ F.map g)
        rw [F.map_comp]
      | add f g hf hg => simp only [_root_.map_add, hf, hg]
    | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
@[simp] private theorem liftLinear_tmul (F : C ⥤ D) [F.Additive] [F.Linear R]
    {X Y : ScalarLocalization R C p} (a : Localization.Away p) (f : X.obj ⟶ Y.obj) :
    (liftLinear R p F).map (a ⊗ₜ[R] f) = a ⊗ₜ[R] F.map f := by
  change (F.mapLinearMap R).baseChange (Localization.Away p) (a ⊗ₜ[R] f) = _
  simpa only [CategoryTheory.Functor.coe_mapLinearMap] using
    (LinearMap.baseChange_tmul (F.mapLinearMap R) a f)

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private instance liftLinear_additive (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (liftLinear R p F).Additive where
  map_add {X Y f g} := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (f + g) = _
    exact _root_.map_add _ f g

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def liftAdjunction (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (adj : F ⊣ G) :
    liftLinear R p F ⊣ liftLinear R p G where
  unit :=
    { app X := 1 ⊗ₜ[R] adj.unit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.comp_obj]
        change composition R C p _ _ _
          (1 ⊗ₜ[R] adj.unit.app Y.obj) f =
          composition R C p _ _ _
            ((G.mapLinearMap R).baseChange (Localization.Away p)
              ((F.mapLinearMap R).baseChange (Localization.Away p) f))
            (1 ⊗ₜ[R] adj.unit.app X.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, CategoryTheory.Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.unit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app X := 1 ⊗ₜ[R] adj.counit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.comp_obj]
        change composition R D p _ _ _
          (1 ⊗ₜ[R] adj.counit.app Y.obj)
            ((F.mapLinearMap R).baseChange (Localization.Away p)
              ((G.mapLinearMap R).baseChange (Localization.Away p) f)) =
          composition R D p _ _ _ f (1 ⊗ₜ[R] adj.counit.app X.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, CategoryTheory.Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.counit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components X := by
    change composition R D p _ _ _ (1 ⊗ₜ[R] adj.counit.app (F.obj X.obj))
      ((liftLinear R p F).map (1 ⊗ₜ[R] adj.unit.app X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.left_triangle_components X.obj)
  right_triangle_components X := by
    change composition R C p _ _ _
      ((liftLinear R p G).map (1 ⊗ₜ[R] adj.counit.app X.obj))
      (1 ⊗ₜ[R] adj.unit.app (G.obj X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.right_triangle_components X.obj)
end Rationalization

namespace CommonOpenHeartProof
open IntegralSupportNormalization FrobeniusExchange CategoryTheory.Functor

section LinearLeft
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C}
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem linearLeftOfLinearRight (R : Type*) [CommRing R] [Linear R C] [Linear R D]
    [G.Linear R] (a : F ⊣ G) : F.Linear R where
  map_smul {X Y} f r := by
    apply (a.homEquiv _ _).injective
    have hh (v : X ⟶ Y) : a.homEquiv _ _ (F.map v) = v ≫ a.unit.app Y := by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality v).symm
    rw [hh, a.homEquiv_unit, G.map_smul, Linear.comp_smul, ← a.homEquiv_unit,
      hh, Linear.smul_comp]

end LinearLeft

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private noncomputable def faithfulIntegralReduction
    {C : Type*} [Category C] {D : Type*} [Category D]
    {Q : Type*} [Category Q]
    (i : C ⥤ D) (hi : i.FullyFaithful)
    {S : D ⥤ Q} {T : Q ⥤ D} (a : S ⊣ T)
    (h : ∀ Y, IsIso (a.unit.app (i.obj Y))) : (i ⋙ S).FullyFaithful where
  preimage {X Y} f := hi.preimage (a.homEquiv _ _ f ≫ inv (a.unit.app (i.obj Y)))
  map_preimage {X Y} f := by
    let := h Y
    change S.map (i.map _) = _
    rw [hi.map_preimage]
    apply (a.homEquiv _ _).injective
    have hh : ∀ g : i.obj X ⟶ i.obj Y,
        a.homEquiv _ _ (S.map g) = g ≫ a.unit.app (i.obj Y) := fun g ↦ by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality g).symm
    rw [hh]
    simp
  preimage_map {X Y} f := by
    let := h Y
    change hi.preimage (a.homEquiv _ _ (S.map (i.map f)) ≫ _) = _
    rw [a.homEquiv_unit]
    have hh := (a.unit.naturality (i.map f)).symm
    change a.unit.app (i.obj X) ≫ T.map (S.map (i.map f)) = _ at hh
    rw [hh]
    simp


section HeartExact
open CategoryTheory.Triangulated
universe uA vA uB vB
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  [IsTriangulated A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B] (t : TStructure A) (s : TStructure B)
  (G : A ⥤ B) [G.CommShift ℤ] [G.IsTriangulated] [G.Additive]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem heartExact
    (P : ObjectProperty A) (Q : ObjectProperty B) (ht : t.heart = P) (hs : s.heart = Q)
    (h : ∀ X, P X → Q (G.obj X)) :
    PreservesFiniteLimits (Q.lift (P.ι ⋙ G) (fun X ↦ h X.obj X.property)) := by
  subst P Q
  let := t.hasHeartFullSubcategory
  let := s.hasHeartFullSubcategory
  let := t.abelianHeart t.heart.FullSubcategory
  let := s.abelianHeart s.heart.FullSubcategory
  let H := s.heart.lift (t.heart.ι ⋙ G) (fun X ↦ h X.obj X.property)
  have : H.Additive := CategoryTheory.Functor.additive_of_comp_faithful _ s.heart.ι
  apply (CategoryTheory.Functor.preservesFiniteLimits_tfae H).out 0 3 |>.mp
  intro S hS
  obtain ⟨δ, hδ⟩ := (t.shortExact_iff_exists_distTriang S).1 hS
  have hh : (S.map H).ShortExact := (s.shortExact_iff_exists_distTriang (S.map H)).2
    ⟨G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app _, G.map_distinguished _ hδ⟩
  exact ⟨hh.exact, hh.mono_f⟩
end HeartExact

namespace StageLeftAdjunction
universe w u₁ v₁ u₂ v₂
variable {I : Type w} [Preorder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {B : I → Type u₂} [∀ i, Category.{v₂} (B i)]
  {S : StageSystem C} {T : StageSystem B}

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem coherenceInv
    (R : StageSystem.Morphism T S)
  (L : ∀ i, C i ⥤ B i) (a : ∀ i, L i ⊣ R.Φ i)
  (b : ∀ {i j : I} (h : i ≤ j), L i ⋙ T.T h ≅ S.T h ⋙ L j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (R.β h).hom.app ((L i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R.Φ j).map ((b h).inv.app K))
    {i j k : I} (h : i ≤ j) (h' : j ≤ k) (K : C i) :
    (L k).map ((S.assoc h h').inv.app K) ≫ (b h').inv.app ((S.T h).obj K) ≫
      (T.T h').map ((b h).inv.app K) =
    (b (h.trans h')).inv.app K ≫ (T.assoc h h').inv.app ((L i).obj K) := by
  apply ((a k).homEquiv _ _).injective
  change (a k).unit.app _ ≫ (R.Φ k).map _ =
    (a k).unit.app _ ≫ (R.Φ k).map _
  simp only [CategoryTheory.Functor.map_comp]
  have hunit := (a k).unit.naturality ((S.assoc h h').inv.app K)
  dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hunit
  rw [← reassoc_of% hunit]
  rw [← reassoc_of% (hb h' ((S.T h).obj K))]
  have hn := (R.β h').hom.naturality ((b h).inv.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] at hn
  rw [← hn, ← (S.T h').map_comp_assoc, ← hb, (S.T h').map_comp]
  have ht := (S.assoc h h').inv.naturality ((a i).unit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at ht
  simp only [Category.assoc]
  rw [← reassoc_of% ht]
  have hc := R.coh h h' ((L i).obj K)
  have hc' : (S.T h').map ((R.β h).hom.app ((L i).obj K)) ≫
      (R.β h').hom.app ((T.T h).obj ((L i).obj K)) =
    (S.assoc h h').hom.app ((R.Φ i).obj ((L i).obj K)) ≫
      (R.β (h.trans h')).hom.app ((L i).obj K) ≫
      (R.Φ k).map ((T.assoc h h').inv.app ((L i).obj K)) := by
    rw [← reassoc_of% hc]
    simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hc']
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (hb (h.trans h') K)]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def family
    (R : StageSystem.Morphism T S)
  (L : ∀ i, C i ⥤ B i) (a : ∀ i, L i ⊣ R.Φ i)
  (b : ∀ {i j : I} (h : i ≤ j), L i ⋙ T.T h ≅ S.T h ⋙ L j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (R.β h).hom.app ((L i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R.Φ j).map ((b h).inv.app K)) : S.Morphism T where
  Φ := L
  β := b
  coh {i j k} h h' K := by
    apply (cancel_epi ((L k).map ((S.assoc h h').inv.app K) ≫
      (b h').inv.app ((S.T h).obj K) ≫ (T.T h').map ((b h).inv.app K))).1
    rw [Category.assoc, Category.assoc, ← (T.T h').map_comp_assoc,
      Iso.inv_hom_id_app]
    change (L k).map ((S.assoc h h').inv.app K) ≫
      (b h').inv.app ((S.T h).obj K) ≫
      (T.T h').map (𝟙 ((L j).obj ((S.T h).obj K))) ≫
      (b h').hom.app ((S.T h).obj K) ≫ (L k).map ((S.assoc h h').hom.app K) = _
    simp only [(T.T h').map_id]
    rw [coherenceInv R L a b hb]
    simp

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def familyUnit
    (R : StageSystem.Morphism T S)
  (L : ∀ i, C i ⥤ B i) (a : ∀ i, L i ⊣ R.Φ i)
  (b : ∀ {i j : I} (h : i ≤ j), L i ⋙ T.T h ≅ S.T h ⋙ L j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (R.β h).hom.app ((L i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R.Φ j).map ((b h).inv.app K)) :
    StageSystem.Morphism.Hom (StageSystem.Morphism.id S)
    ((family R L a b hb).comp R) where
  τ i := (a i).unit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (S.T h).map ((a i).unit.app K) ≫
      ((R.β h).hom.app ((L i).obj K) ≫ (R.Φ j).map ((b h).hom.app K)) =
      𝟙 _ ≫ (a j).unit.app ((S.T h).obj K)
    rw [Category.id_comp, ← Category.assoc, hb, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    change (a j).unit.app ((S.T h).obj K) ≫
      (R.Φ j).map (𝟙 ((L j).obj ((S.T h).obj K))) = _
    rw [(R.Φ j).map_id]
    exact Category.comp_id (X := (S.T h).obj K)
      (Y := (R.Φ j).obj ((L j).obj ((S.T h).obj K))) _

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def familyCounit
    (R : StageSystem.Morphism T S)
  (L : ∀ i, C i ⥤ B i) (a : ∀ i, L i ⊣ R.Φ i)
  (b : ∀ {i j : I} (h : i ≤ j), L i ⋙ T.T h ≅ S.T h ⋙ L j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (R.β h).hom.app ((L i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R.Φ j).map ((b h).inv.app K))
    (hc : ∀ {i j : I} (h : i ≤ j) (K : B i),
      (L j).map ((R.β h).hom.app K) ≫ (a j).counit.app ((T.T h).obj K) =
        (b h).inv.app ((R.Φ i).obj K) ≫ (T.T h).map ((a i).counit.app K)) :
    StageSystem.Morphism.Hom (R.comp (family R L a b hb)) (StageSystem.Morphism.id T) where
  τ i := (a i).counit
  comm {i j} h K := by
    simp only [StageSystem.Morphism.id_β_hom_app, StageSystem.Morphism.comp_β_hom_app]
    change (T.T h).map ((a i).counit.app K) ≫ 𝟙 _ =
      ((b h).hom.app ((R.Φ i).obj K) ≫ (L j).map ((R.β h).hom.app K)) ≫
        (a j).counit.app ((T.T h).obj K)
    rw [Category.comp_id, Category.assoc, hc, Iso.hom_inv_id_app_assoc]

end StageLeftAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def descendStageAdjunction
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : StageSystem.Morphism T S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η :
    StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit) :
    L.functor ⊣ R.functor where
  unit := StageSystem.Morphism.functorIdIso.inv ≫
    StageSystem.Morphism.descNatTrans η ≫ (L.functorCompIso R).hom
  counit := (R.functorCompIso L).inv ≫
    StageSystem.Morphism.descNatTrans ε ≫ StageSystem.Morphism.functorIdIso.hom
  left_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (T.ι X.stage).map ((L.Φ X.stage).map ((a X.stage).unit.app X.obj)) ≫
      (T.ι X.stage).map ((a X.stage).counit.app ((L.Φ X.stage).obj X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (T.ι X.stage).map _ =
      𝟙 ((T.ι X.stage).obj ((L.Φ X.stage).obj X.obj))
    calc
      _ = (T.ι X.stage).map (𝟙 ((L.Φ X.stage).obj X.obj)) :=
        congrArg ((T.ι X.stage).map) ((a X.stage).left_triangle_components X.obj)
      _ = _ := (T.ι X.stage).map_id _
  right_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (S.ι X.stage).map ((a X.stage).unit.app ((R.Φ X.stage).obj X.obj)) ≫
      (S.ι X.stage).map ((R.Φ X.stage).map ((a X.stage).counit.app X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (S.ι X.stage).map _ =
      𝟙 ((S.ι X.stage).obj ((R.Φ X.stage).obj X.obj))
    calc
      _ = (S.ι X.stage).map (𝟙 ((R.Φ X.stage).obj X.obj)) :=
        congrArg ((S.ι X.stage).map) ((a X.stage).right_triangle_components X.obj)
      _ = _ := (S.ι X.stage).map_id _


section LeftMate
variable {A B C D' : Type*} [Category A] [Category B] [Category C] [Category D']
  {L : A ⥤ B} {P : B ⥤ A} {L' : C ⥤ D'} {P' : D' ⥤ C}
  (a : L ⊣ P) (a' : L' ⊣ P') [IsIso a.unit] [IsIso a'.unit]
  (S : A ⥤ C) (T' : B ⥤ D') (g : P ⋙ S ≅ T' ⋙ P')
  (e : L ⋙ T' ≅ S ⋙ L')

include e in
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem leftMate_isIso :
    IsIso (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ g.hom)).natTrans) := by
  let : L'.Full := a'.fullyFaithfulLOfIsIsoUnit.full
  let : L'.Faithful := a'.fullyFaithfulLOfIsIsoUnit.faithful
  let d := ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ g.hom)).natTrans
  have hd (K : A) : IsIso (d.app K) := by
    have hh : a'.homEquiv _ _ (d.app K) =
        S.map (a.unit.app K) ≫ g.hom.app (L.obj K) := by
      exact (unit_mateEquiv_symm a a' (TwoSquare.mk _ _ _ _ g.hom) K).symm
    have : IsIso (a'.homEquiv _ _ (d.app K)) := by rw [hh]; infer_instance
    have : IsIso (a'.counit.app (T'.obj (L.obj K))) :=
      a'.isIso_counit_app_iff_mem_essImage.mpr
        (CategoryTheory.Functor.essImage.ofIso (e.app K).symm (L'.obj_mem_essImage _))
    have he : d.app K = (a'.homEquiv _ _).symm (a'.homEquiv _ _ (d.app K)) :=
      ((a'.homEquiv _ _).symm_apply_apply _).symm
    rw [he, Adjunction.homEquiv_counit]
    change IsIso (L'.map (a'.homEquiv _ _ (d.app K)) ≫ a'.counit.app (T'.obj (L.obj K)))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end LeftMate

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U T : Scheme.{u}} [baseU : U.Over (Spec (.of D.k))] [baseT : T.Over (Spec (.of D.k))]
  [ftU : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [qcU : QuasiCompact (U ↘ Spec (.of D.k))]
  [ftT : LocallyOfFiniteType (T ↘ Spec (.of D.k))]
  [qcT : QuasiCompact (T ↘ Spec (.of D.k))]
  (j : U ⟶ T) [oj : IsOpenImmersion j] [overj : j.IsOver (Spec (.of D.k))]

omit [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  [j.IsOver (Spec (.of D.k))] in
include baseT ftT qcT in
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem openQuasiCompact : QuasiCompact j := by
  let : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of D.k))
  let : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of D.k))
  let : IsNoetherian T := {}
  infer_instance

variable [qj : QuasiCompact j]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev integral :=
  sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion j) E

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def realization :
    integral D l hl j E ⋙ (sfIntegralConstructible l E T).ι ≅
      (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j :=
  (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def cohomology (a : ℤ) :
    integral D l hl j E ⋙ (sfIntegralConstructible l E T).ι ⋙
        DerivedCategory.homologyFunctor (scalarReductionSource l E T) a ≅
      (sfIntegralConstructible l E U).ι ⋙
        DerivedCategory.homologyFunctor (scalarReductionSource l E U) a ⋙
          PurCompactSupport.openExtension (PurCompactSupport.completed l E) j :=
  (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (realization D l hl j E) _ ≪≫
    CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (sfIntegralConstructible l E U).ι
      (CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso
        (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j) a).symm

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem integral_standard (b : Bool) (n : ℤ)
    (K : sfIntegralConstructibleCategory l E U)
    (hK : sfIntegralStandardClass l E U b n K) :
    sfIntegralStandardClass l E T b n ((integral D l hl j E).obj K) := by
  intro a ha
  exact ((PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).map_isZero
    (hK a ha)).of_iso ((cohomology D l hl j E a).app K)


attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem reduction_isIso
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ y : T, Invertible (l : T.residueField y)] (K : sfIntegralConstructibleCategory l E U) :
    IsIso ((compactOperationReduction l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) j
      (Compactification.ofIsOpenImmersion j)).app K) := by
  let c := Compactification.ofIsOpenImmersion j
  let a := compactOperationReduction l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) j c
  let S := (models l E).system T
  apply (S.isIso_iff_evaluations _).2
  intro n
  have hh := (compactRealization_existsUnique l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) j c).exists.choose_spec K n
  let V := coefficientSequenceDerivedEvaluation l E T n
  let q := (scalarReductionDerivedExtension l E T n).map
    ((compactRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) j c).hom.app K)
  let e := (S.reductionEvaluation n).inv.app ((compactImage l E j c).obj K.obj)
  let r := V.map ((operationReduction l E
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)).app K.obj)
  let d := (compactFiniteEvaluation l E c n).hom.app K.obj
  have : IsIso (q ≫ e ≫ r ≫ d) := by
    have hh' : q ≫ e ≫ r ≫ d = (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E K n).hom := hh
    rw [hh']
    infer_instance
  have : IsIso (e ≫ r ≫ d) := IsIso.of_isIso_comp_left q _
  have : IsIso (r ≫ d) := IsIso.of_isIso_comp_left e _
  have : IsIso r := IsIso.of_isIso_comp_right r d
  change IsIso (V.map
    (S.reduction.map ((compactRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) j c).hom.app K) ≫
      (operationReduction l E
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)).app K.obj))
  rw [V.map_comp]
  infer_instance

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
@[irreducible] private def integralAdjunction
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ y : T, Invertible (l : T.residueField y)] :
    integral D l hl j E ⊣ constructibleIntegralPullback l E j := by
  let SU := (models l E).system U
  let ST := (models l E).system T
  let iU := (sfIntegralConstructible l E U).ι
  let iT := (sfIntegralConstructible l E T).ι
  let c := Compactification.ofIsOpenImmersion j
  let a := compactOperationReduction l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) j c
  let : ∀ K, IsIso (a.app K) := reduction_isIso D l hl j E
  let := NatIso.isIso_of_isIso_app a
  let e : integral D l hl j E ⋙ (iT ⋙ ST.reduction) ≅
      (iU ⋙ SU.reduction) ⋙ systemDerivedOpen l E j :=
    asIso a ≪≫ isoWhiskerLeft (iU ⋙ SU.reduction)
      (isoWhiskerLeft (systemDerivedOpen l E j) (systemDirectId l E T) ≪≫
        CategoryTheory.Functor.rightUnitor _)
  let t := whiskerLeft iT (integralComparisonPullbackCounit l E j ST SU
    ((models l E).roos U) ((models l E).pullback j))
  let : ∀ K, IsIso (t.app K) := fun K ↦ (models l E).effective j K
  let := NatIso.isIso_of_isIso_app t
  exact (systemDerivedOpenAdjunction l E j).restrictFullyFaithful
    (faithfulIntegralReduction iU (sfIntegralConstructible l E U).fullyFaithfulι
      SU.adjunction ((models l E).complete U))
    (faithfulIntegralReduction iT (sfIntegralConstructible l E T).fullyFaithfulι
      ST.adjunction ((models l E).complete T)) e.symm (asIso t).symm



attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
@[irreducible] private def integralFullyFaithful : (integral D l hl j E).FullyFaithful := by
  apply Classical.choice
  let R := PurCompactSupport.completed l E
  obtain ⟨e, ⟨he⟩⟩ := PurCompactSupport.openExtension_derivedSlicePresentation R j
  let L := (SheafOfModules.localizedModuleExtension.{u} (R.ring T)
    (ProEt.mk j)).mapDerivedCategory
  let a := SheafOfModules.localizedModuleDerivedAdjunction.{u} (R.ring T) (ProEt.mk j)
  let : IsIso a.unit := SheafOfModules.localizedDerivedUnit_isIso j (R.ring T)
  let : L.Full := a.fullyFaithfulLOfIsIsoUnit.full
  let : L.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  let : (ordinaryOpen l E j).Full := CategoryTheory.Functor.Full.of_iso he.symm
  let : (ordinaryOpen l E j).Faithful := CategoryTheory.Functor.Faithful.of_iso he.symm
  let : (integral D l hl j E ⋙ (sfIntegralConstructible l E T).ι).Full :=
    CategoryTheory.Functor.Full.of_iso (realization D l hl j E).symm
  let : (integral D l hl j E ⋙ (sfIntegralConstructible l E T).ι).Faithful :=
    CategoryTheory.Functor.Faithful.of_iso (realization D l hl j E).symm
  exact ⟨CategoryTheory.Functor.FullyFaithful.ofCompFaithful
    (G := (sfIntegralConstructible l E T).ι)
    (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful _)⟩

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
@[irreducible] private def rationalAdjunction
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ y : T, Invertible (l : T.residueField y)] :
    (sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j) E ⊣ rationalDerivedPullback l E j) ×
    (sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j) E).FullyFaithful := by
  apply Classical.choice
  let I := integral D l hl j E
  let P := constructibleIntegralPullback l E j
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  let a := integralAdjunction D l hl j E
  obtain ⟨Q, ⟨b⟩, hadd, hlin⟩ := sfIntegralPullbackLinearAdjunction l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) j
  have : Q.Additive := hadd
  have : Q.Linear R := hlin
  have : P.Additive := b.left_adjoint_additive
  have : P.Linear R := linearLeftOfLinearRight R b
  have : I.Additive := a.left_adjoint_additive
  have : I.Linear R := linearLeftOfLinearRight R a
  let J := Rationalization.liftLinear R p I
  let Pq := Rationalization.liftLinear R p P
  have heq : Pq = rationalDerivedPullback l E j := by
    apply (rationalDerivedPullback_existsUnique l E j).unique _
      (rationalDerivedPullback_existsUnique l E j).exists.choose_spec
    refine ⟨inferInstance, (fun _ ↦ rfl), ?_⟩
    intro K N b c
    exact heq_of_eq (Rationalization.liftLinear_tmul R p P c b)
  have hJ : J = sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j) E := by
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  rw [← hJ, ← heq]
  let b := Rationalization.liftAdjunction R p I P a
  let : I.Full := (integralFullyFaithful D l hl j E).full
  let : I.Faithful := (integralFullyFaithful D l hl j E).faithful
  let : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  have hu (K : sfRationalConstructibleCategory l E U) : IsIso (b.unit.app K) := by
    change IsIso ((CategoryTheory.ScalarLocalization.localization R _ p).map
      (a.unit.app K.obj))
    infer_instance
  let : IsIso b.unit := NatIso.isIso_of_isIso_app _
  exact ⟨⟨b, b.fullyFaithfulLOfIsIsoUnit⟩⟩

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem rational_standard (b : Bool) (n : ℤ)
    (K : sfRationalConstructibleCategory l E U)
    (hK : sfRationalStandardClass l E U b n K) :
    sfRationalStandardClass l E T b n
      ((sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
        (Compactification.ofIsOpenImmersion j) E).obj K) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨(integral D l hl j E).obj M, integral_standard D l hl j E b n M hM, ?_⟩
  exact ⟨(sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion j) E).mapIso e⟩

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  [∀ x : U, Invertible (l : U.residueField x)]
  [∀ y : T, Invertible (l : T.residueField y)]
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
attribute [local instance] stageCategory
attribute [local implicit_reducible] catToReflQuiver StageHom
set_option allowUnsafeReducibility true in
attribute [local reducible] Stage stageCategory
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
set_option allowUnsafeReducibility true in
attribute [local irreducible] stageSystem commonStageDerivedPullback
  sfCompactSupportFiniteFunctor rationalDerivedPullback

include D hl baseU ftU qcU baseT ftT qcT oj overj qj in
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
set_option Elab.async false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem commonAdjunction :
    ∃ J : generalAlgebraicallyClosedConstructibleCategory l Ω U ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω T,
      Nonempty (J ⊣ commonStageDerivedPullback l Ω j) ∧
      (∀ (b : Bool) (n : ℤ)
        (K : generalAlgebraicallyClosedConstructibleCategory l Ω U),
        sfCommonStageStandardClass l U Ω b n K →
        sfCommonStageStandardClass l T Ω b n (J.obj K)) := by
  let : ∀ E : Index l Ω, Category (Stage l Ω U E) :=
    fun E ↦ stageCategory l Ω U E
  let : ∀ E : Index l Ω, Category (Stage l Ω T E) :=
    fun E ↦ stageCategory l Ω T E
  obtain ⟨⟨Φ, β, coh⟩, hR, _⟩ := sfRationalDirectImageCoefficientCompatibility l Ω j
  obtain ⟨hΦ, hβ, _⟩ := hR
  dsimp only at hΦ hβ
  subst Φ
  let R : (stageSystem l Ω T).Morphism (stageSystem l Ω U) :=
    ⟨(fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) j), β, coh⟩
  let L : ∀ E : Index l Ω, Stage l Ω U E ⥤ Stage l Ω T E :=
    fun E ↦ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) (Compactification.ofIsOpenImmersion j)
        (Coefficient.{u} l Ω E)
  let a : ∀ E, L E ⊣ R.Φ E := fun E ↦
    (rationalAdjunction D l hl j (Coefficient.{u} l Ω E)).1
  let hf (E : Index l Ω) : (L E).FullyFaithful :=
    (rationalAdjunction D l hl j (Coefficient.{u} l Ω E)).2
  have hu (E : Index l Ω) : IsIso (a E).unit := by
    let : (L E).Full := (hf E).full
    let : (L E).Faithful := (hf E).faithful
    exact (a E).unit_isIso_of_L_fully_faithful
  let e : ∀ {E F : Index l Ω} (h : E ≤ F),
      L E ⋙ (stageSystem l Ω T).T h ≅ (stageSystem l Ω U).T h ⋙ L F :=
    fun {E F} h ↦
      let hβ := sfCompactSupportNormalizedScalarIsomorphisms l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl)
        (Compactification.ofIsOpenImmersion j) Ω E F h
      let β := hβ.choose_spec.2.2.choose
      isoWhiskerLeft _ (operationStageTransitionIso l Ω T E F h) ≪≫ β ≪≫
        isoWhiskerRight (operationStageTransitionIso l Ω U E F h).symm _
  let d := fun {E F : Index l Ω} (h : E ≤ F) ↦
    ((mateEquiv (a E) (a F)).symm (TwoSquare.mk _ _ _ _ (R.β h).hom)).natTrans
  have hd {E F : Index l Ω} (h : E ≤ F) : IsIso (d h) := by
    let := hu E
    let := hu F
    exact leftMate_isIso (a E) (a F) _ _ (R.β h) (e h)
  let b := fun {E F : Index l Ω} (h : E ≤ F) ↦ (@asIso _ _ _ _ (d h) (hd h)).symm
  have hb {E F : Index l Ω} (h : E ≤ F) (K : Stage l Ω U E) :
      ((stageSystem l Ω U).T h).map ((a E).unit.app K) ≫
        (R.β h).hom.app ((L E).obj K) =
      (a F).unit.app (((stageSystem l Ω U).T h).obj K) ≫
        (R.Φ F).map ((b h).inv.app K) :=
    unit_mateEquiv_symm (a E) (a F) (TwoSquare.mk _ _ _ _ (R.β h).hom) K
  have hc {E F : Index l Ω} (h : E ≤ F) (K : Stage l Ω T E) :
      (L F).map ((R.β h).hom.app K) ≫
        (a F).counit.app (((stageSystem l Ω T).T h).obj K) =
      (b h).inv.app ((R.Φ E).obj K) ≫
        ((stageSystem l Ω T).T h).map ((a E).counit.app K) :=
    mateEquiv_counit_symm (a E) (a F) (TwoSquare.mk _ _ _ _ (R.β h).hom) K
  let J := StageLeftAdjunction.family R L a b hb
  let adj := descendStageAdjunction J R a
    (StageLeftAdjunction.familyUnit R L a b hb)
    (StageLeftAdjunction.familyCounit R L a b hb hc) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hReq : R.functor = commonStageDerivedPullback l Ω j := by
    unfold commonStageDerivedPullback
    apply (commonStageDerivedPullback_existsUnique l Ω j).unique
      (y₁ := R.functor)
    · constructor
      · intro K; rfl
      · intro K N M hK hN f
        apply heq_of_eq
        rw [StageSystem.Morphism.functor_map_mkHom]
        dsimp only [StageSystem.Morphism.mapAt, R]
        have hp := congrArg Iso.hom (eq_of_heq (hβ K.stage M hK K.obj))
        have hq := congrArg Iso.inv (eq_of_heq (hβ N.stage M hN N.obj))
        dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
        erw [hp, hq]
        rfl
    · exact (commonStageDerivedPullback_existsUnique l Ω j).exists.choose_spec
  refine ⟨J.functor, ⟨adj.ofNatIsoRight (eqToIso hReq)⟩, ?_⟩
  intro q n K hK
  obtain ⟨E, M, hM, ⟨α⟩⟩ := hK
  refine ⟨E, (L E).obj M, rational_standard D l hl j
    (Coefficient.{u} l Ω E) q n M hM, ?_⟩
  exact ⟨J.functor.mapIso α ≪≫ (J.ιCompFunctorIso E).symm.app M⟩

end CommonOpenHeartProof

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
/-- Exact open extension on the underlying constructible heart, before ind-completion
or Frobenius structures.
Source: SGA 4, XVII, §5; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-zl-common-stage-open-heart-adjunction).
Proof: the finite-type schemes over the field are Noetherian, so the open immersion
is quasi-compact. At each positive finite coefficient level, extension by zero is
exact, preserves constructible cohomology and its cohomological interval, and is
left adjoint to restriction. Apply this functor to the complete quotient tower.
Its open unit and counit commute with the quotient transitions; the normalized
Roos comparison identifies the resulting complete object with ordinary open
extension. Restrict to constructible objects, then rationalize the adjunction:
on Hom groups the bijection is additive and linear, hence extends to fractions.
Completed finite scalar extension commutes with open extension by the tensor-unit
comparison, and carries the unit and counit to their scalar extensions. Descend
these functors and the two transformations to the common-stage category by
representing every arrow at one finite field. The triangle identities are checked
there. Standard cohomology is computed at a common finite stage, where extension
by zero is exact, so the descended functor preserves the heart and is exact on it.
Full faithfulness of the heart inclusion identifies the given restriction functor
with this restriction, using hF. Transfer the adjunction across that identification.
The argument includes the empty open, the identity immersion, and zero objects;
no separatedness of either scheme over the field is used. -/
theorem commonStageOpenHeartAdjunction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {U T : Scheme.{u}} [U.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (j : U ⟶ T) [IsOpenImmersion j] [j.IsOver (Spec (.of D.k))]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ y : T, Invertible (l : T.residueField y)]
    (F : sfCommonStageHeart l T Ω ⥤ sfCommonStageHeart l U Ω)
    (hF : F ⋙ (sfCommonStageHeartProperty l U Ω).ι =
      (sfCommonStageHeartProperty l T Ω).ι ⋙ commonStageDerivedPullback l Ω j) :
    ∃ J : sfCommonStageHeart l U Ω ⥤ sfCommonStageHeart l T Ω,
      PreservesFiniteLimits J ∧ PreservesFiniteColimits J ∧ Nonempty (J ⊣ F) := by
  let : QuasiCompact j := CommonOpenHeartProof.openQuasiCompact D j
  obtain ⟨J, ⟨a⟩, hJ⟩ := CommonOpenHeartProof.commonAdjunction D l hl j Ω
  let P := sfCommonStageHeartProperty l U Ω
  let Q := sfCommonStageHeartProperty l T Ω
  let t := sfCommonStageStandardTStructure l U Ω D hl
  let s := sfCommonStageStandardTStructure l T Ω D hl
  have ht : t.heart = P := (sfCommonStageHeart_properties l U Ω D hl).1
  have hs : s.heart = Q := (sfCommonStageHeart_properties l T Ω D hl).1
  have hh (K) (hK : P K) : Q (J.obj K) :=
    ⟨hJ true 0 K hK.1, hJ false 0 K hK.2⟩
  let H := Q.lift (P.ι ⋙ J) (fun K ↦ hh K.obj K.property)
  let b : H ⊣ F := a.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (eqToIso hF).symm
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨cf, _, _, _, _, _, hc⟩ :=
    (automorphismConstructibleStage_descended_shifts l Ω C j
      (Iso.refl T) (Iso.refl U) (by simp)).2
  let : (commonStageDerivedPullback l Ω j).CommShift ℤ := cf
  let : (commonStageDerivedPullback l Ω j).IsTriangulated := hc.1
  let : J.CommShift ℤ := a.leftAdjointCommShift ℤ
  let : a.CommShift ℤ := a.commShift_of_rightAdjoint ℤ
  let : J.IsTriangulated := a.isTriangulated_leftAdjoint
  let : (commonStageDerivedPullback l Ω j).Additive := inferInstance
  let : J.Additive := a.left_adjoint_additive
  have : PreservesFiniteLimits H :=
    CommonOpenHeartProof.heartExact t s J P Q ht hs hh
  have : H.IsLeftAdjoint := b.isLeftAdjoint
  exact ⟨H, inferInstance, inferInstance, ⟨b⟩⟩

end WeilConjectures
