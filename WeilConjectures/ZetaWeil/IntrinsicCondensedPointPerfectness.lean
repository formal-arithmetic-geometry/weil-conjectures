/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointPerfectness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointPerfectness
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricPointSectionsTransport
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.CurrentAdmissibleScalarRealization.CurrentAdmissibleScalarRealizationExact
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing

/-! # Point perfectness for intrinsic condensed constructible inputs

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
thm-pod-point-perfectness.md and its proof (blueprint: thm-pod-point-perfectness).

These statements use the intrinsic ordinary condensed Dctf of def-sf-setting and
def-weil-finite-tor-amplitude. The coefficient complexes, scalar duals, reduction functors,
and canonical compact-to-ordinary mate are the existing constructions. The earlier
constant-model theorems have a different input predicate and do not state this interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

local instance pointProfiniteEssentiallySmall :
    EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
local instance pointSiteEssentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Embed the finite coefficient extension in the fixed algebraic closure. Uniqueness of
its extended norm makes the induced ring equivalence an isometry; applying continuous maps
on each profinite object gives the condensed coefficient isomorphism.
Source: thm-pod-point-perfectness, Step 3, identification of a finite coefficient field
(blueprint: thm-pod-point-perfectness). -/
private theorem rational_coefficient_model (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (sfRationalCoefficient l E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let f : E →ₐ[Padic l] PadicAlgCl l := IsAlgClosed.lift
  let F : PadicAlgCl.FiniteIntermediateField l :=
    ⟨f.fieldRange, Module.Finite.equiv f.equivFieldRange.toLinearEquiv⟩
  let e : E ≃+* F := f.equivFieldRange.toRingEquiv
  let v : AbsoluteValue E ℝ :=
    (NormedField.toAbsoluteValue (PadicAlgCl l)).comp f.toRingHom.injective
  have hv (a : Padic l) : v (algebraMap (Padic l) E a) = ‖a‖ := by
    change ‖f (algebraMap (Padic l) E a)‖ = ‖a‖
    rw [f.commutes]
    exact PadicAlgCl.norm_extends l a
  have he : Isometry e :=
    AddMonoidHomClass.isometry_of_norm e (spectralNorm_unique_field_norm_ext hv)
  have hei : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let eR : Profinite.continuousCoefficientRingSheaf E ≅
      Profinite.continuousMapRingSheaf.{u} F :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hei.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S g
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S g
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let eA := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eA.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  exact ⟨F, ⟨Mon.mkIso' eA⟩⟩

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

set_option maxHeartbeats 2000000 in
-- Explicit tensor-amplitude instances expand the native condensed module category.
set_option maxHeartbeats 2000000 in
-- Integral scalar extension expands the native graded tensor instances.
set_option synthInstance.maxHeartbeats 400000 in
-- Integral scalar change expands the fourfold graded tensor instance.
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
end AlgebraicGeometry.ProEtale.CondensedRing
