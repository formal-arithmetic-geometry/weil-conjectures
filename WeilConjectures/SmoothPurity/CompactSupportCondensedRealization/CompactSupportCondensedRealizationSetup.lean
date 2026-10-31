/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjection
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.SemilinearCompactSupportCoefficientTransport
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData

import WeilConjectures.SmoothPurity.Normalized.NormalizedRealizationIntegralScalar
import WeilConjectures.SmoothPurity.Normalized.NormalizedRealizationSectionScalar
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientGeneralPullbackIso
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.OperationScalarTransportNormalization
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.NormalizedSectionEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Compact-support reconstruction models and coefficient encodings

Source: Bhatt--Scholze 6.7.2, 6.7.6--6.7.17 and blueprint
sk-thm-purity-transport, Steps 2--3. These are the original setup declarations of
CompactSupportCondensedRealization, separated to keep each file within the compile limit.
(blueprint: lem-pur-compact-support-condensed-realization-setup).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict completed-coefficient tower is constructed by reduction, whole-system
proper/open operations, and the dependency's exact coefficient restriction.
Source: blueprint proof Step 3; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def strictTower {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) :=
  R.reduction ⋙ systemSupport l E c ⋙ coefficientSequenceDerivedRestriction.{u, u} l E Y

/-- The actual total derived limit of that strict tower, transported through the
published completed-coefficient presentation. No vertex of a bare derived-category
cone is selected. Source: blueprint proof Step 3; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def rawSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived Y (pbcIntegralDatum l E) :=
  (purCoefficientModel l E X).functor ⋙ strictTower l E c R ⋙
    coefficientConstantTowerLimit.{u, u} l E Y ⋙ (purCoefficientModel l E Y).inverse

/-- Integral reconstruction data. The underlying functor is literally the total-limit
composite just defined; the reduction isomorphism below will be its counit.
Source: blueprint proof Steps 1--3; Bhatt--Scholze 6.7.2 and 6.7.7
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
structure IntegralModel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W) where
  preserves : ∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K →
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((rawSupport l E c (R X)).obj K)
  [additive : (rawSupport l E c (R X)).Additive]
  [linear : (rawSupport l E c (R X)).Linear (PbcIntegralRing l E)]
  [commShift : (rawSupport l E c (R X)).CommShift ℤ]
  triangulated :
    @Functor.IsTriangulated
      (PbcCompletedDerived X (pbcIntegralDatum l E))
      (PbcCompletedDerived Y (pbcIntegralDatum l E))
      _ _ _ _ (rawSupport l E c (R X))
      commShift
      inferInstance inferInstance inferInstance inferInstance
      (inferInstance : ∀ n : ℤ,
        (shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) n).Additive)
      (inferInstance : ∀ n : ℤ,
        (shiftFunctor (PbcCompletedDerived Y (pbcIntegralDatum l E)) n).Additive)
      inferInstance inferInstance
  towerEvaluation : ∀ n : ℕ,
    strictTower l E c (R X) ⋙
        pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
      compactSupportRestrictedLevel l E c n
  towerTransition : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
    (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        ((strictTower l E c (R X)).obj K) ≫ (towerEvaluation n).hom.app K =
      (towerEvaluation m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K
  normalized : ∀ K : CondensedERealization.Integral l E X,
    IsNormalizedCoefficientSequence.{u, u} l E Y
      ((systemSupport l E c).obj
        ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)))

/-- Restriction of the actual total-limit functor to the recorded integral categories.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def integralSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    CondensedERealization.Integral l E X ⥤ CondensedERealization.Integral l E Y :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
      rawSupport l E c (R X))
    (fun K ↦ M.preserves K.obj K.property)

/-- The reconstructed semilinear compact-support system on an integral input.
Source: blueprint proof Steps 2--3
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def reconstructedSystem {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (_M : IntegralModel l E c R) :
    CondensedERealization.Integral l E X ⥤ coefficientSequenceDerived.{u, u} l E Y :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
    (purCoefficientModel l E X).functor ⋙ (R X).reduction ⋙
      systemSupport l E c

/-- The limit presentation retains the canonical counit of the coefficient equivalence.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def limitPresentation {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    integralSupport l E c R M ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E Y).functor ≅
      reconstructedSystem l E c R M ⋙ coefficientSequenceLimit.{u, u} l E Y :=
  Functor.isoWhiskerLeft
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
      (purCoefficientModel l E X).functor ⋙ (R X).reduction ⋙
        systemSupport l E c ⋙ coefficientSequenceLimit.{u, u} l E Y)
    (purCoefficientModel l E Y).counitIso

/-- Alpha is the actual reduction/limit counit, preceded by the canonical limit
presentation. Its evaluated adjuncts are therefore the total-limit projections.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def alpha {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    integralSupport l E c R M ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E Y).functor ⋙ (R Y).reduction ⟶
      reconstructedSystem l E c R M :=
  Functor.whiskerRight (limitPresentation l E c R M).hom (R Y).reduction ≫
    Functor.whiskerLeft (reconstructedSystem l E c R M) (R Y).adjunction.counit

attribute [local irreducible] strictTower rawSupport integralSupport reconstructedSystem
  limitPresentation alpha

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]

/-- Every finite coefficient embedding is continuous for the extended p-adic topology.
Source: Bhatt--Scholze 6.8.1; blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: regard the embedding as a linear map over Q_l. Its source is finite dimensional,
so the finite-dimensional normed-space continuity theorem applies. -/
theorem coefficientEmbedding_continuous (i : E →ₐ[ℚ_[l]] F) : Continuous i := by
  exact i.toLinearMap.continuous_of_finiteDimensional

/-- The coefficient sheaf map is postcomposition by the given field embedding on
continuous functions. Both the source and target retain the scheme coefficient universe.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def fieldRingMap (i : E →ₐ[ℚ_[l]] F) :
    Profinite.continuousCoefficientRingSheaf E ⟶
      Profinite.continuousCoefficientRingSheaf F :=
  ⟨{ app := fun S ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         ((i.toRingHom.compLeftContinuous S.unop
           (coefficientEmbedding_continuous l E F i)).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same canonical coefficient change on internal ring objects.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def fieldMap (i : E →ₐ[ℚ_[l]] F) :
    Profinite.continuousCoefficientRingObj E ⟶ Profinite.continuousCoefficientRingObj F :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (fieldRingMap l E F i)

/-- Postcomposition preserves the internal unit and multiplication.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the map comes from a morphism of ring sheaves, so it preserves pointwise
multiplication and the constant unit; the forgetful sheaf functor retains these equations. -/
theorem fieldMap_isMonHom (i : E →ₐ[ℚ_[l]] F) : IsMonHom (fieldMap l E F i) := by
  unfold fieldMap
  infer_instance

attribute [instance] fieldMap_isMonHom

private def coefficientRangeRingIso (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    Profinite.continuousCoefficientRingSheaf E ≅
      Profinite.continuousMapRingSheaf.{u} i.fieldRange := by
  let e := i.equivFieldRange
  have hc : Continuous e := i.toLinearMap.continuous_of_finiteDimensional.subtype_mk _
  have : FiniteDimensional ℚ_[l] i.fieldRange := Module.Finite.equiv e.toLinearEquiv
  have hd : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  refine
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop hc).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hd).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply RingCat.hom_ext
    apply RingHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply (f.down x)
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply RingCat.hom_ext
    apply RingHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (f.down x)

/-- Finite coefficient tensor is exact in the original internal-module categories.
Source: blueprint proof Step 6; finite-free coefficient calculus
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: choose a basis of F over E. The coordinate maps are continuous, hence give the
continuous F-valued coefficient ring as a finite free E-valued module. Inverse image
from the point retains that description, and tensor is a finite direct sum. -/
theorem fieldExtension_flat (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (fieldMap l E F i) W)) := by
  let j : F →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  let jE : E →ₐ[ℚ_[l]] PadicAlgCl l := j.comp i
  let KE : PadicAlgCl.FiniteIntermediateField l :=
    ⟨jE.fieldRange, Module.Finite.equiv jE.equivFieldRange.toLinearEquiv⟩
  let KF : PadicAlgCl.FiniteIntermediateField l :=
    ⟨j.fieldRange, Module.Finite.equiv j.equivFieldRange.toLinearEquiv⟩
  have h : KE ≤ KF := by
    rintro x ⟨y, rfl⟩
    exact ⟨i y, rfl⟩
  let H := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let eE := coefficientRangeRingIso l E jE
  let eF := coefficientRangeRingIso l F j
  let a := (upperStarFromPoint W).map (H.map eE.hom)
  let b := AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap W l h
  let c := (upperStarFromPoint W).map (H.map eF.inv)
  have : IsMonHom a := by dsimp only [a]; infer_instance
  have : IsIso a := by dsimp only [a]; infer_instance
  have : IsMonHom c := by dsimp only [c]; infer_instance
  have : IsIso c := by dsimp only [c]; infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv a).symm
  have : PreservesFiniteLimits (Mod.extendScalars b) :=
    CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap l h (X := W)
  have : PreservesFiniteLimits (Mod.extendScalars c) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv c).symm
  have habc : coefficientMap (fieldMap l E F i) W = a ≫ b ≫ c := by
    change (upperStarFromPoint W).map _ =
      (upperStarFromPoint W).map _ ≫ (upperStarFromPoint W).map _ ≫
        (upperStarFromPoint W).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (upperStarFromPoint W).map
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact (j.equivFieldRange.symm_apply_apply (i (f.down x))).symm
  have : PreservesFiniteLimits (Mod.extendScalars (b ≫ c)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsComp b c).symm
  exact preservesFiniteLimits_of_natIso
    ((Mod.extendScalarsIsoOfEq habc) ≪≫ Mod.extendScalarsComp a (b ≫ c)).symm

attribute [instance] fieldExtension_flat

/-- Continuity of an embedding into the algebraic closure, with no coefficient-universe
restriction. Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the embedding is Q_l-linear with finite-dimensional source. The usual linear-map
continuity theorem applies even when the target has infinite Q_l dimension. -/
theorem omegaEmbedding_continuous (i : E →ₐ[ℚ_[l]] PadicAlgCl l) : Continuous i := by
  exact i.toLinearMap.continuous_of_finiteDimensional

/-- A continuous E-valued section remains valued in one finite subextension after embedding.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the algebraic image of E is a finite intermediate field of Qbar_l. The value at
every point belongs to this same image. This proves the defining finite-subfield-valued
condition, including on empty profinite test spaces. -/
theorem omegaEmbedding_finiteValued (i : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (S : Profinite.{u}) (a : C(S, E)) :
    (i.toRingHom.compLeftContinuous S (omegaEmbedding_continuous l E i)) a ∈
      PadicAlgCl.finiteIntermediateFieldValued l S := by
  refine ⟨i.fieldRange, ?_, fun x ↦ ⟨a x, rfl⟩⟩
  exact Module.Finite.equiv i.equivFieldRange.toLinearEquiv

/-- The actual finite-subfield-valued algebraic-closure coefficient map. It does not
replace Omega by the larger sheaf of all continuous Omega-valued functions.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def omegaRingMap (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    Profinite.continuousCoefficientRingSheaf E ⟶ Profinite.padicAlgClCondensedRing l :=
  ⟨{ app := fun S ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((i.toRingHom.compLeftContinuous S.unop (omegaEmbedding_continuous l E i)).codRestrict
           (PadicAlgCl.finiteIntermediateFieldValued l S.unop)
           (omegaEmbedding_finiteValued l E i S.unop)).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The algebraic-closure map on the actual internal ring objects.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def omegaMap (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    Profinite.continuousCoefficientRingObj E ⟶ Profinite.padicAlgClRingObj.{u} l :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (omegaRingMap l E i)

/-- The finite-valued coefficient embedding is a morphism of internal rings.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: codomain restriction keeps the pointwise ring operations. Forgetting a ring-sheaf
map to its underlying abelian-sheaf map therefore preserves unit and multiplication. -/
theorem omegaMap_isMonHom (i : E →ₐ[ℚ_[l]] PadicAlgCl l) : IsMonHom (omegaMap l E i) := by
  unfold omegaMap
  infer_instance

attribute [instance] omegaMap_isMonHom

/-- Extension to finite-valued algebraic-closure coefficients is flat.
Source: blueprint proof Steps 13--14
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: express the coefficient object as the filtered union of finite intermediate
extensions containing the image of E. Each stage is finite free over E. Tensor commutes
with this filtered colimit; exact filtered colimits of module sheaves give flatness. -/
theorem omegaExtension_flat (i : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (omegaMap l E i) W)) := by
  let e := coefficientRangeRingIso l E i
  let H := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let a := (upperStarFromPoint W).map (H.map e.hom)
  have : IsMonHom a := by dsimp only [a]; infer_instance
  have : IsIso a := by dsimp only [a]; infer_instance
  let K : PadicAlgCl.FiniteIntermediateField l :=
    ⟨i.fieldRange, Module.Finite.equiv i.equivFieldRange.toLinearEquiv⟩
  let b := AlgebraicGeometry.ProEtale.padicSubfieldRingObjToPadicAlgCl W l K
  have : PreservesFiniteLimits (Mod.extendScalars b) :=
    CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
      l K (X := W)
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv a).symm
  have hab : coefficientMap (omegaMap l E i) W = a ≫ b := by
    change (upperStarFromPoint W).map _ =
      (upperStarFromPoint W).map _ ≫ (upperStarFromPoint W).map _
    rw [← Functor.map_comp]
    apply congrArg (upperStarFromPoint W).map
    ext S f
    rfl
  exact preservesFiniteLimits_of_natIso
    ((Mod.extendScalarsIsoOfEq hab) ≪≫ Mod.extendScalarsComp a b).symm

attribute [instance] omegaExtension_flat

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
end WeilConjectures.CompactSupportCondensedRealization

attribute [local irreducible]
  WeilConjectures.CompactSupportCondensedRealization.strictTower
  WeilConjectures.CompactSupportCondensedRealization.rawSupport
  WeilConjectures.CompactSupportCondensedRealization.integralSupport
  WeilConjectures.CompactSupportCondensedRealization.limitPresentation
  WeilConjectures.CompactSupportCondensedRealization.alpha
  WeilConjectures.CompactSupportCondensedRealization.fieldRingMap
  WeilConjectures.CompactSupportCondensedRealization.fieldMap
  WeilConjectures.CompactSupportCondensedRealization.omegaRingMap
  WeilConjectures.CompactSupportCondensedRealization.omegaMap

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Restricting the actual additive total-limit functor is additive.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the integral categories are full additive subcategories. Their inclusion is
faithful, and the underlying map is exactly the additive rawSupport map. -/
theorem integralSupport_additive {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) : (integralSupport l E c R M).Additive := by
  let := M.additive
  unfold integralSupport
  infer_instance

attribute [instance] integralSupport_additive

/-- Restricting the normalized constant-scalar total-limit action retains R-linearity.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: scalar multiplication in the integral full subcategory is inherited from the
ambient completed module category. Faithfulness of inclusion reduces linearity to
IntegralModel.linear, with precisely the same constant R-sections. -/
theorem integralSupport_linear {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    (integralSupport l E c R M).Linear (PbcIntegralRing l E) := by
  let := M.linear
  unfold integralSupport
  refine ⟨fun f r ↦ ?_⟩
  apply ObjectProperty.hom_ext
  exact (rawSupport l E c (R X)).map_smul r f.hom

attribute [instance] integralSupport_linear

/-- The actual raw scalar localization of integral compact support, on localized morphisms.
Source: blueprint proof Steps 4--5; rational transport
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def rationalSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    CondensedERealization.Rational l E X ⥤ CondensedERealization.Rational l E Y :=
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E)
    (integralSupport l E c R M)

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [hp : Fact (ringChar k).Prime] [hl : Fact (ringChar k ≠ l)]

/-- The separated finite-type schemes in the coefficient-realization statement are
Noetherian. Source: blueprint proof Step 1
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: Spec(k) is Noetherian and the structure morphism is finite type. Apply the
finite-type-over-Noetherian theorem; separatedness is not needed for this implication. -/
theorem base_noetherian (T : CondensedERealization.Base k) : IsNoetherian T.scheme := by
  let : IsLocallyNoetherian T.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.scheme ↘ Spec (.of k))
  let : CompactSpace T.scheme :=
    QuasiCompact.compactSpace_of_compactSpace (T.scheme ↘ Spec (.of k))
  exact ⟨⟩

attribute [instance] base_noetherian

/-- The existing finite-type dimension bound, used for the recorded scalar functor.
Source: blueprint proof Step 1; lem-kun-dimension-finite-type
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: finite type over the zero-dimensional field spectrum gives finite Krull dimension.
The published dimension theorem supplies one natural-number upper bound. -/
theorem base_dimension (T : CondensedERealization.Base k) :
    ∃ n : ℕ, topologicalKrullDim T.scheme ≤ n := by
  exact exists_topologicalKrullDim_le (T.scheme ↘ Spec (.of k))

include hp hl in
/-- The coefficient prime is a unit in every stalk of a k-scheme.
Source: blueprint proof Step 1
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the positive characteristic of k is prime and differs from l, so the image of l
in k is nonzero. Its inverse maps to an inverse in every local ring of the scheme. -/
theorem base_primeUnit (T : CondensedERealization.Base k) :
    ∀ x : T.scheme, IsUnit (l : T.scheme.presheaf.stalk x) := by
  intro x
  have h : IsUnit (l : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime)
      (Fact.out : ringChar k ≠ l))
  have hΓ := h.map
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (T.scheme ↘ Spec (.of k)).appTop).hom)
  simpa only [map_natCast] using hΓ.map (T.scheme.presheaf.germ ⊤ x trivial).hom

/-- The comparison datum at the fixed geometric compactification. The system arrow is
literally the total-limit counit alpha, and the field functor is the archived ambient
proper/open composite. Source: blueprint proof Steps 1--5
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
structure RealizationAt (D : CondensedERealization.Data l E k)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) where
  integral : IntegralModel l E c R
  alpha_isIso : IsIso (alpha l E c R integral)
  field_preserves : ∀ K : CondensedERealization.Ambient E X.scheme,
    boundedConstructible (CondensedERealization.Coefficient E X.scheme) K →
      boundedConstructible (CondensedERealization.Coefficient E Y.scheme)
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj E) c).obj K)
  realization : rationalSupport l E c R integral ⋙ (D.atObject Y).realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι ≅
      (D.atObject X).realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient E X.scheme)).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.continuousCoefficientRingObj E) c

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Existence of the section- and universal-counit-normalized scalar transport.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the two ordinary scalar models are the same sheafified balanced tensor
construction. The identity on pure tensors gives their natural isomorphism.
Localizing on K-flat representatives gives the derived isomorphism, normalized
by the actual universal tensor counit on every complex. These are exactly the
tensor and counit fields of the recorded OperationScalarTransport interface. -/
theorem scalarModelTransport_nonempty (W : Scheme.{u}) :
    Nonempty (OperationScalarTransport l E F i W) := by
  exact operationScalarTransport_nonempty l E F i W

/-- The recorded transport, determined uniquely by its tensor and counit fields.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def scalarModelTransport (W : Scheme.{u}) : OperationScalarTransport l E F i W :=
  (scalarModelTransport_nonempty l E F i W).some

/-- The published coefficient-model scalar comparison followed by the recorded
normalized transport from exact scalar extension to its universal K-flat model.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def scalarPresentation (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙ (purCoefficientModel l F W).functor ≅
      (purCoefficientModel l E W).functor ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i W) :=
  purScalarModel l E F i W ≪≫
    Functor.isoWhiskerLeft (purCoefficientModel l E W).functor
      (scalarModelTransport l E F i W).derived

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The recorded completed integral scalar functor, with the inherited finite-type
bounds. Its comparison with strict Koszul/Roos scalar extension is the published chi.
Source: blueprint proof Step 7; def-weil-integral-scalar-extension
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def integralScalar (T : CondensedERealization.Base k) :
    CondensedERealization.Integral l E T.scheme ⥤
      CondensedERealization.Integral l F T.scheme :=
  pbcEmbeddingIntegralTensor l E F i T.scheme (base_dimension k T) (base_primeUnit l k T)

/-- Integral reduction into the actual full derived semilinear category.
Source: blueprint proof Steps 2--3
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def integralReduction (T : CondensedERealization.Base k)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E T.scheme) :
    CondensedERealization.Integral l E T.scheme ⥤
      DerivedCategory (coefficientSequenceModules.{u, u} l E T.scheme) :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
    (purCoefficientModel l E T.scheme).functor ⋙ R.reduction

universe uI uJ uA uB uC uD uS uT vI vJ vA vB vC vD vS vT

/-- Compose the inclusion, coefficient-presentation and reduction comparisons, with
all intermediate categories and functors explicit. This is precisely the three-factor
canonical comparison used below.
Source: blueprint proof Steps 10--11
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def pasteReductionComparison
    {I : Type uI} {J : Type uJ} {A : Type uA} {B : Type uB}
    {C : Type uC} {D : Type uD} {S : Type uS} {T : Type uT}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vA} A] [Category.{vB} B]
    [Category.{vC} C] [Category.{vD} D] [Category.{vS} S] [Category.{vT} T]
    (iE : I ⥤ A) (iF : J ⥤ B) (sI : I ⥤ J) (sA : A ⥤ B)
    (mE : A ⥤ C) (mF : B ⥤ D) (sC : C ⥤ D)
    (rE : C ⥤ S) (rF : D ⥤ T) (sS : S ⥤ T)
    (inclusion : sI ⋙ iF ≅ iE ⋙ sA)
    (presentation : sA ⋙ mF ≅ mE ⋙ sC)
    (reduction : sC ⋙ rF ≅ rE ⋙ sS) :
    sI ⋙ iF ⋙ mF ⋙ rF ≅ iE ⋙ mE ⋙ rE ⋙ sS :=
  Functor.isoWhiskerRight inclusion (mF ⋙ rF) ≪≫
    Functor.isoWhiskerLeft iE
      (Functor.isoWhiskerRight presentation rF ≪≫ Functor.isoWhiskerLeft mE reduction)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical full-system balancing comparison for integral scalar extension.
Source: blueprint proof Steps 10--11
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def integralReductionScalar (T : CondensedERealization.Base k)
    (RE : CoefficientDerivedSystemCalculus.{u, u} l E T.scheme)
    (RF : CoefficientDerivedSystemCalculus.{u, u} l F T.scheme) :
    integralScalar l E F i k T ⋙ integralReduction l F k T RF ≅
      integralReduction l E k T RE ⋙ (systemScalarData l E F i T.scheme).scalar.T := by
  letI : Fact (∃ n : ℕ, topologicalKrullDim T.scheme ≤ n) := ⟨base_dimension k T⟩
  letI : Fact (∀ x : T.scheme, IsUnit (l : T.scheme.presheaf.stalk x)) :=
    ⟨base_primeUnit l k T⟩
  exact pasteReductionComparison
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l F)))
    (integralScalar l E F i k T) (pbcEmbeddingAmbientTensor l E F i T.scheme)
    (purCoefficientModel l E T.scheme).functor (purCoefficientModel l F T.scheme).functor
    (pbcDerivedExtend (completedCoefficientMap l E F i T.scheme))
    RE.reduction RF.reduction (systemScalarData l E F i T.scheme).scalar.T
    (pbcIntegralScalarInclusionIso l E F i T.scheme)
    (scalarPresentation l E F i T.scheme) (reductionScalar l E F i T.scheme RE RF)

/-- Compatibility with alpha is an equality on the entire derived semilinear system,
using the canonical scalar projection and the reduction/limit adjunction balancing.
Source: blueprint proof Steps 10--11
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def IsIntegralScalarSquare
    (RE : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (RF : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l F W)
    (X Y : CondensedERealization.Base k) {f : X.scheme ⟶ Y.scheme} (c : Compactification f)
    (ME : IntegralModel l E c RE) (MF : IntegralModel l F c RF)
    (s : integralSupport l E c RE ME ⋙ integralScalar l E F i k Y ≅
      integralScalar l E F i k X ⋙ integralSupport l F c RF MF) : Prop :=
  ∀ K : CondensedERealization.Integral l E X.scheme,
    (integralReduction l F k Y (RF Y.scheme)).map (s.hom.app K) ≫
        (alpha l F c RF MF).app ((integralScalar l E F i k X).obj K) =
      (integralReductionScalar l E F i k Y (RE Y.scheme) (RF Y.scheme)).hom.app
          ((integralSupport l E c RE ME).obj K) ≫
        (systemScalarData l E F i Y.scheme).scalar.T.map ((alpha l E c RE ME).app K) ≫
        (systemProjection l E F i c).app
          ((integralReduction l E k X (RE X.scheme)).obj K) ≫
        (systemSupport l F c).map
          ((integralReductionScalar l E F i k X (RE X.scheme) (RF X.scheme)).inv.app K)

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

attribute [local irreducible] IsIntegralScalarSquare

/-- The section-ring map induced by the actual internal coefficient map.
Source: Stacks 00YV; blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: apply the coefficient morphism to each underlying abelian-sheaf section.
Its internal unit and multiplication equations make this a section-ring homomorphism.
Naturality is the sheaf-map naturality. The specified section functions determine the
map uniquely, so no additional coefficient identification is chosen. -/
theorem sectionFieldMap_existsUnique (W : Scheme.{u}) :
    ∃! d : CondensedERealization.SectionRing E W ⟶ CondensedERealization.SectionRing F W,
      ∀ (U : W.ProEtᵒᵖ) (x : (CondensedERealization.SectionRing E W).obj.obj U),
        HEq (d.hom.app U x) ((coefficientMap (fieldMap l E F i) W).hom.app U x) := by
  let : IsCommMonObj (CondensedERealization.Coefficient E W) :=
    isCommMonObj_condensedRingObj (Profinite.continuousCoefficientRingObj E) W
  let : IsCommMonObj (CondensedERealization.Coefficient F W) :=
    isCommMonObj_condensedRingObj (Profinite.continuousCoefficientRingObj F) W
  refine ⟨CondensedRing.sectionRingMap W
    (coefficientMap (fieldMap l E F i) W), ?_, ?_⟩
  · intro U x
    rfl
  · intro d hd
    ext U x
    exact eq_of_heq (hd U x)

/-- The unique actual map on reconstructed section rings.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def sectionFieldMap (W : Scheme.{u}) :
    CondensedERealization.SectionRing E W ⟶ CondensedERealization.SectionRing F W :=
  (sectionFieldMap_existsUnique l E F i W).exists.choose

/-- Coefficient transport of that same section-ring map through the normalized charts.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def realizedFieldMap (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :=
  AE.sectionIso.inv ≫ sectionFieldMap l E F i W ≫ AF.sectionIso.hom

/-- The completed/field coefficient square commutes for the specified inclusions.
Source: blueprint proof Step 12; continuous coefficient realizations
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: at every test object, both maps send a completed integral section to its
pointwise image under i. The integral and section chart normalizations identify these
functions. Equality on every section proves the ring-sheaf square. -/
theorem realizedCoefficient_square (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    pbcScalarCoefficientMap l E F i W ≫ AF.integralIso.hom ≫ AF.inclusion =
      (AE.integralIso.hom ≫ AE.inclusion) ≫ realizedFieldMap l E F i W AE AF := by
  apply (cancel_epi AE.integralIso.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply Sheaf.hom_ext
  ext U b
  apply rationalCoefficientValue_ext l F W U
  intro x
  have hi := normalizedRealizationIntegralScalar l E F i W AE AF U b x
  have hs := normalizedRealizationSectionScalar l E F i
    (coefficientEmbedding_continuous l E F i) W AE AF (fieldMap l E F i)
    (by intro S f x; unfold fieldMap fieldRingMap; rfl) (sectionFieldMap l E F i W)
    (sectionFieldMap_existsUnique l E F i W).exists.choose_spec U
    (AE.sectionIso.inv.hom.app U (AE.inclusion.hom.app U b)) x
  have hinv : AE.sectionIso.hom.hom.app U
      (AE.sectionIso.inv.hom.app U (AE.inclusion.hom.app U b)) =
        AE.inclusion.hom.app U b :=
    congrArg (fun z ↦ z.hom.app U (AE.inclusion.hom.app U b)) AE.sectionIso.inv_hom_id
  change rationalCoefficientValue l F W U
      (AF.inclusion.hom.app U
        ((AE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i W ≫
          AF.integralIso.hom).hom.app U b)) x =
    rationalCoefficientValue l F W U
      (AF.sectionIso.hom.hom.app U ((sectionFieldMap l E F i W).hom.app U
        (AE.sectionIso.inv.hom.app U (AE.inclusion.hom.app U b)))) x
  rw [AF.inclusion_normalization U.unop _ x, hs, hinv,
    AE.inclusion_normalization U.unop b x]
  exact hi

/-- The existing section encoding, with the two derived-category Hom sizes explicit.
Source: blueprint proof Step 12; lem-weil-pbc-condensed-e-realization
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def encodingDerived (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    CondensedERealization.Ambient E W ⥤
      DerivedCategory (pbcModules W (rationalCoefficientSheaf l W E)) :=
  letI := A.encodingAdditive
  letI := A.encodingInverseAdditive
  (CondensedERealization.moduleEncoding l E W A.sectionIso).functor.mapDerivedCategory

universe wEncoding wEncodingInv

private theorem derivedEncoding_equivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wEncoding} C] [HasDerivedCategory.{wEncodingInv} D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  let ec := e.mapHomologicalComplex (.up ℤ)
  let F := e.functor.mapHomologicalComplex (.up ℤ)
  let G := e.inverse.mapHomologicalComplex (.up ℤ)
  let α : (F ⋙ DerivedCategory.Q) ⋙ e.inverse.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F e.inverse.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.unitIso.symm DerivedCategory.Q ≪≫
      Functor.leftUnitor _
  let β : (G ⋙ DerivedCategory.Q) ⋙ e.functor.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G e.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.counitIso DerivedCategory.Q ≪≫
      Functor.leftUnitor _
  exact Localization.isEquivalence
    (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (.up ℤ))
    (F ⋙ DerivedCategory.Q) e.functor.mapDerivedCategory
    (G ⋙ DerivedCategory.Q) e.inverse.mapDerivedCategory α β

/-- The derived section encoding remains an equivalence at the displayed Hom sizes.
Source: Stacks 00YV and 06YY; blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: the ordinary section encoding is an additive equivalence. Apply its functor
and inverse degreewise to complexes and localize both at quasi-isomorphisms. The
localized ordinary unit and counit give the derived unit and counit, at the two
independent derived-category universes, and their triangle identities descend. -/
theorem encodingDerived_isEquivalence (W : Scheme.{u})
    (A : CondensedERealization.At l E W) :
    (encodingDerived l E W A).IsEquivalence := by
  let := A.encodingAdditive
  let := A.encodingInverseAdditive
  exact derivedEncoding_equivalence (CondensedERealization.moduleEncoding l E W A.sectionIso)

attribute [instance] encodingDerived_isEquivalence

/-- The ordinary encoding/restriction square is identity on all module sections.
Source: Stacks 00YV; blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: both encoded module actions are obtained by restricting the same internal
coefficient action. The definition of realizedFieldMap identifies those actions.
The identity section maps are therefore linear, natural and mutually inverse;
sectionwise faithfulness proves uniqueness. -/
theorem encodingRestriction_existsUnique (W : Scheme.{u})
    (AE : CondensedERealization.At l E W) (AF : CondensedERealization.At l F W) :
    ∃! d : Mod.comap (coefficientMap (fieldMap l E F i) W) ⋙
          (CondensedERealization.moduleEncoding l E W AE.sectionIso).functor ≅
        (CondensedERealization.moduleEncoding l F W AF.sectionIso).functor ⋙
          pbcRestrict (realizedFieldMap l E F i W AE AF),
      ∀ (M : Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
        (CondensedERealization.Coefficient F W)) (U : W.ProEtᵒᵖ)
        (x : (((Mod.comap (coefficientMap (fieldMap l E F i) W) ⋙
          (CondensedERealization.moduleEncoding l E W AE.sectionIso).functor).obj M).val.obj U)),
        HEq ((d.hom.app M).val.app U x) x := by
  let : IsCommMonObj (CondensedERealization.Coefficient E W) :=
    isCommMonObj_condensedRingObj (Profinite.continuousCoefficientRingObj E) W
  let : IsCommMonObj (CondensedERealization.Coefficient F W) :=
    isCommMonObj_condensedRingObj (Profinite.continuousCoefficientRingObj F) W
  have hmap : sectionFieldMap l E F i W =
      CondensedRing.sectionRingMap W (coefficientMap (fieldMap l E F i) W) := by
    apply (sectionFieldMap_existsUnique l E F i W).unique
    · exact (sectionFieldMap_existsUnique l E F i W).exists.choose_spec
    · intro U x
      rfl
  exact normalizedEncodingRestriction W _ _ (coefficientMap (fieldMap l E F i) W)
    (sectionFieldMap l E F i W) hmap _ _ AE.sectionIso AF.sectionIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact localization of the section-normalized coefficient restriction square.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def encodingRestriction (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    (Mod.comap (coefficientMap (fieldMap l E F i) W)).mapDerivedCategory ⋙
        encodingDerived l E W AE ≅
      encodingDerived l F W AF ⋙ pbcDerivedRestrict (realizedFieldMap l E F i W AE AF) :=
  letI := AE.encodingAdditive
  letI := AF.encodingAdditive
  Functor.mapDerivedCategorySquareIso
    (F₁ := Mod.comap (coefficientMap (fieldMap l E F i) W))
    (F₂ := (CondensedERealization.moduleEncoding l E W AE.sectionIso).functor)
    (G₁ := (CondensedERealization.moduleEncoding l F W AF.sectionIso).functor)
    (G₂ := pbcRestrict (realizedFieldMap l E F i W AE AF))
    (encodingRestriction_existsUnique l E F i W AE AF).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar/encoding comparison, obtained by the tensor-adjunction mate.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def encodingScalarMap (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    encodingDerived l E W AE ⋙ pbcDerivedExtend (realizedFieldMap l E F i W AE AF) ⟶
      condensedScalar (fieldMap l E F i) W ⋙ encodingDerived l F W AF :=
  letI := AE.encodingAdditive
  letI := AF.encodingAdditive
  ((mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (fieldMap l E F i) W))
    (pbcDerivedScalarAdjunction (realizedFieldMap l E F i W AE AF))).symm
      (TwoSquare.mk _ (encodingDerived l F W AF) (encodingDerived l E W AE) _
        (encodingRestriction l E F i W AE AF).hom)).natTrans

/-- The normalized encoding scalar mate is invertible.
Source: blueprint proof Step 12; Stacks 06YY
(blueprint: lem-pur-compact-support-condensed-realization-setup).
Proof: both derived section encodings are equivalences. The specified normalized
restriction comparison is an isomorphism of the two right-adjoint composites.
The inverse-mate theorem for equivalences makes its mate an isomorphism. This mate
is exactly encodingScalarMap for the displayed scalar adjunctions. -/
theorem encodingScalarMap_isIso (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    IsIso (encodingScalarMap l E F i W AE AF) := by
  let := AE.encodingAdditive
  let := AF.encodingAdditive
  let : (encodingDerived l E W AE).IsEquivalence := encodingDerived_isEquivalence l E W AE
  let : (encodingDerived l F W AF).IsEquivalence := encodingDerived_isEquivalence l F W AF
  unfold encodingScalarMap
  exact isIso_inverseMate_of_equivalences _ _ (encodingRestriction l E F i W AE AF)

attribute [local irreducible] encodingScalarMap

attribute [instance] encodingScalarMap_isIso

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coefficient-extension comparison on integral lattices, descended through
the fully faithful field encoding. All its factors are specified tensor comparisons.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization-setup). -/
def latticeScalar (T : CondensedERealization.Base k)
    (AE : CondensedERealization.At l E T.scheme) (AF : CondensedERealization.At l F T.scheme) :
    integralScalar l E F i k T ⋙
        pbcRationalization T.scheme (pbcIntegralDatum l F) (pbcUniformizer l F) ⋙
        AF.realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient F T.scheme)).ι ≅
      pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        AE.realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient E T.scheme)).ι ⋙
        (condensedScalar (fieldMap l E F i) T.scheme) :=
  by
  letI := AE.encodingAdditive
  letI := AF.encodingAdditive
  letI := AF.encodingInverseAdditive
  exact Functor.fullyFaithfulCancelRight
    (encodingDerived l F T.scheme AF)
    (Functor.isoWhiskerLeft (integralScalar l E F i k T) AF.scalarExtension ≪≫
      Functor.isoWhiskerLeft
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)))
        (PurCompactSupport.tensorSquare (pbcScalarCoefficientMap l E F i T.scheme)
          (realizedFieldMap l E F i T.scheme AE AF) (AE.integralIso.hom ≫ AE.inclusion)
          (AF.integralIso.hom ≫ AF.inclusion) (realizedCoefficient_square l E F i T.scheme AE AF))
      ≪≫ Functor.isoWhiskerRight AE.scalarExtension.symm
        (pbcDerivedExtend (realizedFieldMap l E F i T.scheme AE AF)) ≪≫
      Functor.isoWhiskerLeft
        (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
          AE.realization.functor ⋙
          (boundedConstructible (CondensedERealization.Coefficient E T.scheme)).ι)
        (asIso (encodingScalarMap l E F i T.scheme AE AF)))

end WeilConjectures.CompactSupportCondensedRealization
