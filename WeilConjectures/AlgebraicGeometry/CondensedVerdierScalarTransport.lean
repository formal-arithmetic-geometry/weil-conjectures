/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Exact symmetric scalar transport for Verdier normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

variable {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]

/-- The ordinary total derived extension along a coefficient isomorphism.
Source: blueprint coefficient normalization in finite biduality
(blueprint: lem-sf-condensed-verdier-scalar-transport). -/
abbrev condensedVerdierScalarTransport (e : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap e.hom.hom X)).leftDerivedFunctor

/-- The canonical K-flat monoidal structure, without a new global instance.
Source: blueprint coefficient normalization in finite biduality
(blueprint: lem-sf-condensed-verdier-scalar-transport). -/
@[instance_reducible] def condensedVerdierScalarMonoidal
    (e : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u}) :
    (condensedVerdierScalarTransport e X).Monoidal :=
  letI := Mod.extendScalarsMonoidal (coefficientMap e.hom.hom X)
  (Mod.extendScalars (coefficientMap e.hom.hom X)).leftDerivedFunctorMonoidal

/-- Scalar transport along an isomorphism is an equivalence preserving the actual
constructible finite-Tor predicate. Its canonical tensor structure respects the
Koszul symmetry and its evaluation-defined closed comparisons are invertible.
Source: latest blueprint, det-pd-biduality-coefficients.proof.md, normalization in (i).
(blueprint: lem-sf-condensed-verdier-scalar-transport).

Proof: extension along an isomorphism is naturally restriction along its inverse,
hence an exact equivalence. Derive it termwise to obtain the unbounded equivalence.
Naturality of coefficient pullback identifies the inverse map with pullback of the
inverse coefficient map. The comparison with termwise inverse restriction and
constantModelCtf_coefficientIso gives preservation of the stated domain. The
canonical derived extension tensorator respects the Koszul swap, as does its
underived tensorator. A strong monoidal equivalence has invertible closed mates,
and an equivalence reflects isomorphisms. No completeness or geometric assumption
is used, and this applies to the zero ring and the empty scheme as well. -/
theorem condensedVerdier_scalar_transport (e : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u}) :
    letI := condensedVerdierScalarMonoidal e X
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X))
    (condensedVerdierScalarTransport e X).IsEquivalence ∧
    (∃ b : (condensedVerdierScalarTransport e X).Braided,
      b.toMonoidal = condensedVerdierScalarMonoidal e X) ∧
    (∀ K : moduleDerived Λ X, dctfPred Λ X K →
      dctfPred Γ X ((condensedVerdierScalarTransport e X).obj K)) ∧
    (∀ K W : moduleDerived Λ X, IsIso
      ((Functor.LaxMonoidal.ihomComparison
        (condensedVerdierScalarTransport e X) K).natTrans.app W)) ∧
    ∀ {K L : moduleDerived Λ X} (f : K ⟶ L),
      IsIso ((condensedVerdierScalarTransport e X).map f) → IsIso f := by
  let φ := coefficientMap e.hom.hom X
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint X).map e.hom.hom))
  have hcomap : (Mod.comap (asIso φ).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_inverse
  have : (Mod.extendScalars φ).IsEquivalence :=
    Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv φ).symm
  have : (condensedVerdierScalarTransport e X).IsEquivalence := by
    unfold condensedVerdierScalarTransport
    infer_instance
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · let := Mod.extendScalarsMonoidal φ
    exact ⟨(Mod.extendScalars φ).leftDerivedFunctorBraided
      (Mod.extendScalars_map_braiding_hom_δ φ), rfl⟩
  · intro K hK
    have hi : inv φ = coefficientMap e.inv.hom X := by
      apply IsIso.inv_eq_of_hom_inv_id
      rw [show φ = coefficientMap e.hom.hom X from rfl, ← coefficientMap_comp]
      change coefficientMap ((Mon.forget _).map (e.hom ≫ e.inv)) X = _
      rw [Iso.hom_inv_id]
      exact coefficientMap_id X
    let d : condensedVerdierScalarTransport e X ≅
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap e.inv.hom X)).mapDerivedCategory :=
      (Mod.extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso
          (Mod.extendScalarsIsoComapInv φ ≪≫ Mod.comapCongr hi)
    have hb := constantModelCtf_coefficientIso e X ⟨K, hK⟩
    have := (constantModelConstructibleFiniteTor_wellDefined Γ X).2.1
    exact ⟨(constantModelBoundedConstructible Γ X).prop_of_iso (d.app K).symm hb.1,
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso (d.app K).symm hb.2⟩
  · intro K W
    infer_instance
  · intro K L f hf
    have := hf
    exact isIso_of_reflects_iso f (condensedVerdierScalarTransport e X)

end AlgebraicGeometry.ProEtale.CondensedRing
