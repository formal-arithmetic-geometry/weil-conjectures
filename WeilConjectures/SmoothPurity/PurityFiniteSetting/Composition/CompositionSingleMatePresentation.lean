/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteCounitProjectionTransport
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-! # Purity in the standing tensor-mate coordinates -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale.CompositionTensorMate

section ProofHelpers

-- Serialize concrete comparisons to bound simultaneous conversion checking.
set_option Elab.async false

set_option cleanup.letToHave false
set_option linter.style.multiGoal false

-- Use the sheaf abelian data cached by the generic six-functor constructions.
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
attribute [local instance 2000] isNoetherian_of_finite
-- Match the coefficient braiding used by the generic derived constructions.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory ProEtale.sheafBraidedCategory

private theorem inverse_square
    {C : Type*} [Category C] {A B U V : C}
    (a : A ≅ B) (b : U ≅ V) (p : A ⟶ U) (q : B ⟶ V)
    [IsIso p] (h : a.hom ≫ q = p ≫ b.hom) : IsIso q := by
  have hq : q = a.inv ≫ p ≫ b.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  rw [hq]
  infer_instance

section DerivedComparison

universe v v₁ v₂

variable {C : Type v₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type v₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

end DerivedComparison

-- Normalize proof-local transport data before checking concrete derived categories.
local syntax (name := startMateProof) "start_mate_proof" : tactic
local syntax (name := finishMateProof) "finish_mate_proof" : tactic

open Lean Meta Elab Tactic in
open Lean Meta Elab Tactic in
attribute [local irreducible] Functor.rightAdjoint Adjunction.ofIsLeftAdjoint

private theorem torAmplitude_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  start_mate_proof
  · refine ⟨h.1, ?_⟩
    intro M N he f hf hN F i hi
    exact h.2 M N (he.map (fun eM ↦ eM ≪≫ e.symm)) f hf hN F i hi
  · finish_mate_proof

private theorem dualizing_boundedConstructible
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    Etale.DerivedCategory.isBoundedConstructible P.Coefficient X
      (Etale.dualizingComplex P.Coefficient f) := by
  start_mate_proof
  · let := P.finiteComparedInvertibleExponent aY
    have hu : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} P.Coefficient) Y (𝟙_ _) := by
      exact ⟨(Etale.DerivedCategory.boundedConstructible _ Y).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0),
        0, 0, (Etale.DerivedCategory.torAmplitudeIn _ Y 0 0).prop_of_iso
          (_root_.DerivedCategory.singleFunctorObjUnitIso _)
          (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
            (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
    have h := (Etale.constructibleFiniteTor_dualizingComplex P.Coefficient aY f hu).1
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (h.2 i), ?_⟩
    obtain ⟨a, ha⟩ := h.1.1
    obtain ⟨b, hb⟩ := h.1.2
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ a).mp ha i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).mp hb i (lt_of_le_of_lt (le_max_right _ _) hi)
  · finish_mate_proof

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.projectionMapOfCompactification ProEtale.projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap ProEtale.rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso
  ProEtale.derivedOpenImmersionLowerShriekProjectionIso

end ProofHelpers

variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

end WeilConjectures.PurityFiniteSetting
