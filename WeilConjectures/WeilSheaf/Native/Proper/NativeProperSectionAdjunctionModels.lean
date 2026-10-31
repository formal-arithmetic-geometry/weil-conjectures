/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Native section adjunction on common resolution models

Source: Stacks 070I, 08BJ; native proper-projection model proof, steps 2--3.
The statement compares only inverse and direct image, without tensor data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open MonoidalCategory
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Read the reconstructed scalar action through ambient scalar forgetting. -/
private theorem section_smul {T : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (R : LocallyFiniteAdicRealization.Realization l T)
    (M : ProEtale.AdicSheaf l T) (V : T.ProEtᵒᵖ)
    (r : (ring l T R).obj.obj V)
    (x : ((sectionFunctor l T R).obj M).val.obj V) :
    r • x =
      (((CategoryTheory.Functor.LaxMonoidal.μ
        (sheafToPresheaf (ProEt.topology T) (WeilCoefficients.{u} l))
        (ProEtale.adicConstantSheaf l T) M.X) ≫
        (sheafToPresheaf (ProEt.topology T) (WeilCoefficients.{u} l)).map
          (Mod.act M.X)).app V) (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x) := by
  change (((CategoryTheory.Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
    (LocallyFiniteAdicRealization.abRing l T)
    ((ProEtale.weilCoefficientsForgetAb l T).obj M.X)) ≫
      (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      (Mod.act (((ProEtale.weilCoefficientsForgetAb l T).mapMod _).obj M).X)).app V).hom
        (r ⊗ₜ[ℤ] x) = _
  simp only [CategoryTheory.Functor.act_mapMod_obj, CategoryTheory.Functor.map_comp,
    ← Category.assoc]
  rw [μ_sheafToPresheaf_comp_map_μ_sheafCompose]
  rfl

/-- The action of native direct image is restriction of the coefficient action.
The tensor generator identity for continuous pushforward is the only monoidal input. -/
private theorem native_push_action {X Y : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (f : X ⟶ Y) (M : ProEtale.AdicSheaf l X) (V : Y.ProEtᵒᵖ)
    (r : (ProEtale.adicConstantSheaf l Y).obj.obj V)
    (x : ((ProEtale.adicLowerStar l f).obj M).X.obj.obj V) :
    (((CategoryTheory.Functor.LaxMonoidal.μ
      (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))
      (ProEtale.adicConstantSheaf l Y) ((ProEtale.adicLowerStar l f).obj M).X) ≫
      (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)).map
        (Mod.act ((ProEtale.adicLowerStar l f).obj M).X)).app V)
        (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x) =
    (((CategoryTheory.Functor.LaxMonoidal.μ
      (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l))
      (ProEtale.adicConstantSheaf l X) M.X) ≫
      (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l)).map
        (Mod.act M.X)).app ((proEtaleBaseChange f).op.obj V))
        (((ProEtale.adicConstantSheafToLowerStar l f).hom.app V r) ⊗ₜ[_] x) := by
  let F := proEtaleBaseChange f
  let J := ProEt.topology Y
  let K := ProEt.topology X
  let A := WeilCoefficients.{u} l
  let P := F.sheafPushforwardContinuous A J K
  let IY := sheafToPresheaf J A
  let ψ := ProEtale.adicConstantSheafToLowerStar l f
  have hn := congr_app (CategoryTheory.Functor.LaxMonoidal.μ_natural_left IY ψ (P.obj M.X)) V
  simp only [NatTrans.comp_app] at hn
  have ht := CategoryTheory.Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    F A J K (ProEtale.adicConstantSheaf l X) M.X V
  change ((CategoryTheory.Functor.LaxMonoidal.μ IY _ _).app V ≫
    (ψ ▷ P.obj M.X).hom.app V ≫ (CategoryTheory.Functor.LaxMonoidal.μ P _ M.X).hom.app V ≫
      (P.map (Mod.act M.X)).hom.app V) (r ⊗ₜ[_] x) = _
  erw [← reassoc_of% hn, reassoc_of% ht]
  rfl

section CounitTransport

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- Changing the two vertical presentations and the chosen left adjoint preserves
an adjunction square's counit equation. -/
private theorem comparison_counit
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {L : C ⥤ D} {U : D ⥤ C} {L' L'' : C' ⥤ D'} {U' : D' ⥤ C'}
    (a : L ⊣ U) (b : L' ⊣ U') (b' : L'' ⊣ U')
    {V V' : C ⥤ C'} {W W' : D ⥤ D'} (v : V ≅ V') (w : W ≅ W')
    (α : V ⋙ L' ≅ L ⋙ W) (δ : U ⋙ V ≅ W ⋙ U')
    (hδ : ∀ X, L'.map (δ.hom.app X) ≫ b.counit.app (W.obj X) =
      α.hom.app (U.obj X) ≫ W.map (a.counit.app X)) (X : D) :
    W'.map (a.counit.app X) =
      ((CategoryTheory.Functor.isoWhiskerLeft L w.symm ≪≫ α.symm ≪≫
        CategoryTheory.Functor.isoWhiskerRight v L' ≪≫
        CategoryTheory.Functor.isoWhiskerLeft V' (b.leftAdjointUniq b')).hom.app (U.obj X)) ≫
      L''.map ((CategoryTheory.Functor.isoWhiskerLeft U v.symm ≪≫ δ ≪≫
        CategoryTheory.Functor.isoWhiskerRight w U').hom.app X) ≫
      b'.counit.app (W'.obj X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app, Category.assoc]
  rw [← (b.leftAdjointUniq b').hom.naturality_assoc]
  simp only [CategoryTheory.Functor.comp_obj]
  rw [b.leftAdjointUniq_hom_app_counit b']
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← L'.map_comp_assoc]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := b.counit.naturality (w.hom.app X)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn
  rw [hn]
  rw [reassoc_of% (hδ X)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← w.inv.naturality_assoc]
  simp

end CounitTransport

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

variable
  (R : LocallyFiniteAdicRealization.Realization l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (S : LocallyFiniteAdicRealization.Realization l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
  (O : Proper.Operations l (NativeBaseChange.geometricMap k₀ p) R S)

/-- The inverse/direct-image part of the normalized section comparison.
Source: Stacks 070I, 08BJ and native proper-projection model proof, steps 2--3
(blueprint: lem-sf-native-proper-section-adjunction-models). -/
structure NativeProperSectionAdjunctionModels where
  pull : nativeOpenPull k₀ l p ⋙ properSectionDerived k₀ l Z R ≅
    properSectionDerived k₀ l Y S ⋙
      ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient
  pushSheaf : lowerStar k₀ l p ⋙ properSectionForget k₀ l Y S ≅
    properSectionForget k₀ l Z R ⋙
      ContinuousRational.DirectImage.modulePush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient
  pushSections : ∀ M V x, HEq ((pushSheaf.hom.app M).val.app V x) x
  push : (lowerStar k₀ l p).rightDerivedFunctor ⋙ properSectionDerived k₀ l Y S ≅
    properSectionDerived k₀ l Z R ⋙
      ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient
  pushRepresentative : ∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
      (_hI : I.IsKInjective),
    (properSectionDerived k₀ l Y S).map (properNativePushUnit k₀ l p I) ≫
      push.hom.app (DerivedCategory.Q.obj I) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          ((properSectionFactors k₀ l Z R).hom.app I) =
    (properSectionFactors k₀ l Y S).hom.app
        (((lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((properPushSheafCochain k₀ l p R S O pushSheaf).hom.app I) ≫
      ContinuousRational.DirectImage.pushUnit (NativeBaseChange.geometricMap k₀ p)
        O.coefficient
        ((properSectionCochain k₀ l Z R).obj I)
  counit : ∀ A,
    (properSectionDerived k₀ l Z R).map
        ((derivedUpperStarLowerStarAdjunction k₀ l p).counit.app A) =
      pull.hom.app ((lowerStar k₀ l p).rightDerivedFunctor.obj A) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (push.hom.app A) ≫
        O.adjunction.counit.app
          ((properSectionDerived k₀ l Z R).obj A)

set_option maxHeartbeats 2000000 in
-- Unfolding the section action and coefficient presentations exceeds the default limit.
omit [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)] in
/-- The coefficient normalization makes the direct-image comparison literally the
identity on sections, including empty site objects. -/
private theorem ordinary_section_push_comparison :
    ∃ b : ProEtale.adicLowerStar l (NativeBaseChange.geometricMap k₀ p) ⋙
        sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S ≅
      sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R ⋙
        ContinuousRational.DirectImage.modulePush
          (NativeBaseChange.geometricMap k₀ p) O.coefficient,
      ∀ M V x, HEq ((b.hom.app M).val.app V x) x := by
  let L := ProEtale.adicLowerStar l (NativeBaseChange.geometricMap k₀ p) ⋙
    sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S
  let T := sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R ⋙
    ContinuousRational.DirectImage.modulePush
      (NativeBaseChange.geometricMap k₀ p) O.coefficient
  have h (M : ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (V : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEtᵒᵖ)
      (r : (ring l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).obj.obj V)
      (x : (L.obj M).val.obj V) :
      r • x = r • (@id ((T.obj M).val.obj V) x) := by
    have hc :
        (ProEtale.adicConstantSheafToLowerStar l
          (NativeBaseChange.geometricMap k₀ p)).hom.app V r =
        (((proEtaleSheafAdjunction (NativeBaseChange.geometricMap k₀ p)
          CommRingCat.{u + 1}).homEquiv _ _ O.coefficient).hom.app V r) := by
      apply ULift.ext
      apply Subtype.ext
      apply ContinuousMap.ext
      intro y
      exact (O.functions V r y).symm
    rw [section_smul, native_push_action]
    change _ =
      (((proEtaleSheafAdjunction (NativeBaseChange.geometricMap k₀ p)
        CommRingCat.{u + 1}).homEquiv _ _ O.coefficient).hom.app V r) •
        (@id (((sectionFunctor l _ R).obj M).val.obj
          ((proEtaleBaseChange (NativeBaseChange.geometricMap k₀ p)).op.obj V)) x)
    rw [section_smul, hc]
    rfl
  let a (M) : L.obj M ⟶ T.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (L.obj M).val) (M₂ := (T.obj M).val)
      (𝟙 _) (fun V r x ↦ h M V r x)⟩
  let b (M) : T.obj M ⟶ L.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (T.obj M).val) (M₂ := (L.obj M).val)
      (𝟙 _) (fun V r x ↦ (h M V r x).symm)⟩
  let e : L ≅ T := NatIso.ofComponents
    (fun M ↦ { hom := a M, inv := b M
               hom_inv_id := by ext V x; rfl
               inv_hom_id := by ext V x; rfl })
    (fun f ↦ by ext V x; rfl)
  exact ⟨e, fun M V x ↦ HEq.rfl⟩

set_option maxHeartbeats 2000000 in
-- Derived-category composition factors involve large localization structures.
set_option linter.unusedSectionVars false in
-- Retain every hypothesis of the published theorem although this proof needs fewer.
/-- The actual sheaf and derived adjunctions agree in section coordinates.
Source: Stacks 070I, 08BJ; BS 6.8.14--6.8.15; native proper-projection model proof,
steps 2--3 (blueprint: lem-sf-native-proper-section-adjunction-models).

Proof: O.functions identifies its coefficient map with precomposition. Thus the
underlying native direct image and ordinary module direct image have the same
sections and action. Their identity comparison is pushSheaf. Taking its left
adjoint mate gives the sheaf inverse-image comparison, with the actual counit
square; the fixed-pair adjunction lift retains these carrier maps. Native inverse
image is exact, as is the section presentation. Localize this sheaf comparison
termwise to obtain pull. On an equivariant K-injective I, forgetting preserves
K-injectivity by the exact integer-orbit left adjoint; the section equivalence
also preserves it. Both direct images are therefore computed by the same complex.
The generic localized mate supplies push, and its unit identity on I is exactly
pushRepresentative, including the two properSectionFactors and the termwise
pushSheaf map. Every derived object is isomorphic to such a K-injective model,
so the mate is invertible everywhere. The composition isomorphisms identify the
localized section functors with the prescribed properSectionDerived functors.
Uniqueness of left adjoints identifies localized ordinary pullback with the left
adjoint chosen in O.adjunction. Its counit identity, together with the derived
mate counit identity and naturality of the composition isomorphisms, gives counit.
No tensor comparison or projection formula is used. The construction also applies to zero
complexes, empty schemes and identity maps. -/
theorem native_proper_section_adjunction_models
    (hR : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (hS : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).IsEquivalence) :
    Nonempty (NativeProperSectionAdjunctionModels k₀ l p R S O) := by
  classical
  let := R.commutative
  let := S.commutative
  let : (sectionFunctor l _ R).Additive := R.sectionsAdditive
  let : (sectionFunctor l _ S).Additive := S.sectionsAdditive
  let := hR
  let := hS
  let E := (sectionFunctor l _ S).asEquivalence
  let H := (sectionFunctor l _ R).asEquivalence
  let f := NativeBaseChange.geometricMap k₀ p
  let F := ProEtale.adicUpperStar l f
  let F' := ContinuousRational.modulePull f O.coefficient
  obtain ⟨b, hb⟩ := ordinary_section_push_comparison k₀ l p R S O
  obtain ⟨q, _hq, _hu, _ht, _hη, hε⟩ := exists_equivalenceAdjunctionComparison E H
    (ProEtale.adicUpperStarLowerStarAdjunction l f) O.moduleAdjunction b
  let e : E.inverse ⋙ F ⋙ H.functor ≅ F' :=
    CategoryTheory.Functor.isoWhiskerLeft E.inverse q ≪≫ E.invFunIdAssoc F'
  have : PreservesFiniteLimits F' := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits F' := preservesFiniteColimits_of_natIso e
  let g := properSectionForget k₀ l Y S
  let h := properSectionForget k₀ l Z R
  let Fw := upperStar k₀ l p
  let Gw := lowerStar k₀ l p
  let G' := ContinuousRational.DirectImage.modulePush f O.coefficient
  let a := upperStarLowerStarAdjunction k₀ l p
  let a' := O.moduleAdjunction
  let qW : Fw ⋙ h ≅ g ⋙ F' := NatIso.ofComponents
    (fun M ↦ q.app M.carrier) (fun t ↦ q.hom.naturality t.hom.f)
  let bW : Gw ⋙ g ≅ h ⋙ G' := NatIso.ofComponents
    (fun M ↦ b.app M.carrier) (fun t ↦ b.hom.naturality t.hom.f)
  have hm : (mateEquiv a a'
      (TwoSquare.mk g Fw F' h qW.symm.hom)).natTrans = bW.hom := by
    apply NatTrans.ext
    funext M
    apply (a'.homEquiv _ _).symm.injective
    change F'.map ((mateEquiv a a' qW.inv).app M) ≫ a'.counit.app _ =
      F'.map (bW.hom.app M) ≫ a'.counit.app _
    rw [mateEquiv_counit]
    exact hε M.carrier
  let α := UnboundedExactTower.localizedSquare Fw F' g h qW.symm
  let δ := (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    a'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk g.mapDerivedCategory Fw.mapDerivedCategory F'.mapDerivedCategory
        h.mapDerivedCategory α.hom)).natTrans
  have hd (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :=
    UnboundedExactTower.localized_mate_cochain_normalization a a' qW.symm I
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have hi (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) [I.IsKInjective] :
      IsIso (δ.app (DerivedCategory.Q.obj I)) := by
    have : CochainComplex.IsKInjective ((h.mapHomologicalComplex (.up ℤ)).obj I) :=
      inferInstance
    have : IsIso (UnboundedExactTower.cochainUnit Gw I) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have : IsIso (UnboundedExactTower.cochainUnit G'
        ((h.mapHomologicalComplex (.up ℤ)).obj I)) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have hc : IsIso ((NatTrans.mapHomologicalComplex bW.hom (.up ℤ)).app I) := by
      change IsIso ((NatIso.mapHomologicalComplex bW (.up ℤ)).hom.app I)
      infer_instance
    have hs : IsIso (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex bW.hom (.up ℤ)).app I) ≫
          UnboundedExactTower.cochainUnit G'
            ((h.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
    have hn := hd I
    rw [hm] at hn
    rw [← hn] at hs
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hs
  have : IsIso δ := by
    have (X : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) : IsIso (δ.app X) := by
      obtain ⟨I, hI, ⟨j⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
      let := hI
      have := hi I
      exact (NatTrans.isIso_app_iff_of_iso δ j).mpr inferInstance
    exact NatIso.isIso_of_isIso_app δ
  let cY : g.mapDerivedCategory ≅ properSectionDerived k₀ l Y S :=
    CategoryTheory.Functor.mapDerivedCategoryCompIso
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
      (sectionFunctor l _ S)
  let cZ : h.mapDerivedCategory ≅ properSectionDerived k₀ l Z R :=
    CategoryTheory.Functor.mapDerivedCategoryCompIso
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
      (sectionFunctor l _ R)
  have cy (I : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
      cY.hom.app (DerivedCategory.Q.obj I) ≫ (properSectionFactors k₀ l Y S).hom.app I =
        g.mapDerivedCategoryFactors.hom.app I := by
    dsimp only [cY, g, properSectionCochain, properSectionForget]
    simpa only [properSectionFactors, properSectionForget, properSectionDerived,
      nativeForget, sectionDerived,
      sectionFunctor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
      CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
      CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id,
      Category.assoc] using
      CategoryTheory.Functor.mapDerivedCategoryCompIso_fac
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
        (sectionFunctor l _ S) I
  have cz (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :
      cZ.hom.app (DerivedCategory.Q.obj I) ≫ (properSectionFactors k₀ l Z R).hom.app I =
        h.mapDerivedCategoryFactors.hom.app I := by
    dsimp only [cZ, h, properSectionCochain, properSectionForget]
    simpa only [properSectionFactors, properSectionForget, properSectionDerived,
      nativeForget, sectionDerived,
      sectionFunctor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
      CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
      CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id,
      Category.assoc] using
      CategoryTheory.Functor.mapDerivedCategoryCompIso_fac
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
        (sectionFunctor l _ R) I
  let push : Gw.rightDerivedFunctor ⋙ properSectionDerived k₀ l Y S ≅
      properSectionDerived k₀ l Z R ⋙ G'.rightDerivedFunctor :=
    CategoryTheory.Functor.isoWhiskerLeft Gw.rightDerivedFunctor cY.symm ≪≫ asIso δ ≪≫
      CategoryTheory.Functor.isoWhiskerRight cZ G'.rightDerivedFunctor
  let t := a'.mapDerivedCategoryRightDerivedAdjunction.leftAdjointUniq O.adjunction
  let pull : nativeOpenPull k₀ l p ⋙ properSectionDerived k₀ l Z R ≅
      properSectionDerived k₀ l Y S ⋙ ContinuousRational.derivedPull f O.coefficient :=
    CategoryTheory.Functor.isoWhiskerLeft Fw.mapDerivedCategory cZ.symm ≪≫ α.symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight cY F'.mapDerivedCategory ≪≫
      CategoryTheory.Functor.isoWhiskerLeft (properSectionDerived k₀ l Y S) t
  refine ⟨⟨pull, bW, ?_, push, ?_, ?_⟩⟩
  · intro M V x
    exact hb M.carrier V x
  · intro I _hI
    have un : UnboundedExactTower.cochainUnit Gw I = properNativePushUnit k₀ l p I := by
      unfold UnboundedExactTower.cochainUnit properNativePushUnit
      change _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫ _ = _
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    have uo : UnboundedExactTower.cochainUnit G'
        ((h.mapHomologicalComplex (.up ℤ)).obj I) =
        ContinuousRational.DirectImage.pushUnit f O.coefficient
          ((properSectionCochain k₀ l Z R).obj I) := by
      unfold UnboundedExactTower.cochainUnit ContinuousRational.DirectImage.pushUnit
      change _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫ _ = _
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    have cb : (NatTrans.mapHomologicalComplex bW.hom (.up ℤ)).app I =
        (properPushSheafCochain k₀ l p R S O bW).hom.app I := by
      ext n
      rfl
    have hn := hd I
    rw [hm, un, uo, cb] at hn
    have ci (J : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) :
        cY.inv.app (DerivedCategory.Q.obj J) =
          (properSectionFactors k₀ l Y S).hom.app J ≫
            g.mapDerivedCategoryFactors.inv.app J := by
      apply (cancel_epi (cY.hom.app (DerivedCategory.Q.obj J))).1
      rw [Iso.hom_inv_id_app, ← Category.assoc, cy, Iso.hom_inv_id_app]
      rfl
    dsimp only [push, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
      CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app, asIso_hom]
    simp only [Category.assoc]
    rw [cY.inv.naturality_assoc]
    rw [← G'.rightDerivedFunctor.map_comp, cz]
    rw [ci]
    simpa only [Category.assoc] using
      congrArg ((properSectionFactors k₀ l Y S).hom.app
        ((Gw.mapHomologicalComplex (.up ℤ)).obj I) ≫ ·) hn
  · intro A
    exact comparison_counit a.mapDerivedCategoryRightDerivedAdjunction
      a'.mapDerivedCategoryRightDerivedAdjunction O.adjunction cY cZ α (asIso δ)
      (fun X ↦ mateEquiv_counit a.mapDerivedCategoryRightDerivedAdjunction
        a'.mapDerivedCategoryRightDerivedAdjunction α.hom X) A

end AlgebraicGeometry.ProEtaleWeilSheaf
