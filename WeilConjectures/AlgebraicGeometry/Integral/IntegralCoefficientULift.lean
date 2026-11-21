/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution

/-!
# Universe lifts of integral coefficient rings

For a finite extension `E` of `ℚ_[l]` living in `Type`, the algebra isomorphism
`E ≃ₐ[ℚ_[l]] ULift E` preserves spectral norms. Hence it identifies the rings of integers
and the condensed rings of continuous maps into them:
`continuousMapRingObj 𝒪_E ≅ DerivedNakayama.integerRing l (ULift E)`, as ring objects.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℚ_[l] E]

variable [FiniteDimensional ℚ_[l] E]

omit [FiniteDimensional ℚ_[l] E] in
/-- The spectral norm on `ULift E` is the spectral norm on `E`. -/
theorem spectralNorm_uliftUp (x : E) :
    spectralNorm ℚ_[l] (ULift.{u} E) (ULift.up x) = spectralNorm ℚ_[l] E x := by
  unfold spectralNorm
  exact congrArg _ (minpoly.algEquiv_eq (ULift.algEquiv.{0, 0, u} (R := ℚ_[l]) (A := E)).symm x)

/-- The universe lift restricts to a ring isomorphism of the rings of integers. -/
noncomputable def uliftIntegersRingEquiv :
    Padic.coefficientExtensionIntegers l E ≃+*
      Padic.coefficientExtensionIntegers l (ULift.{u} E) :=
  (ULift.algEquiv.{0, 0, u} (R := ℚ_[l]) (A := E)).symm.toRingEquiv.restrict _ _ fun x ↦ by
    rw [Padic.mem_coefficientExtensionIntegers, Padic.mem_coefficientExtensionIntegers,
      Padic.coefficientExtensionAbsoluteValue_apply,
      Padic.coefficientExtensionAbsoluteValue_apply]
    exact iff_of_eq (congrArg (· ≤ 1) (spectralNorm_uliftUp l E x).symm)

/-- The universe lift `E → ULift E` is an isometry for the spectral norms. -/
theorem isometry_uliftUp :
    @Isometry E (ULift.{u} E)
      (spectralNorm.normedField ℚ_[l] E).toPseudoMetricSpace.toPseudoEMetricSpace
      (spectralNorm.normedField ℚ_[l] (ULift.{u} E)).toPseudoMetricSpace.toPseudoEMetricSpace
      ULift.up :=
  @Isometry.of_dist_eq _ _ (spectralNorm.normedField ℚ_[l] E).toPseudoMetricSpace
    (spectralNorm.normedField ℚ_[l] (ULift.{u} E)).toPseudoMetricSpace _
    fun x y ↦ spectralNorm_uliftUp l E (x - y)

/-- Postcomposition with a ring isomorphism which is a homeomorphism, on lifted rings of
continuous maps. -/
noncomputable def continuousMapULiftRingEquiv {K L : Type*} [CommRing K] [CommRing L]
    [TopologicalSpace K] [TopologicalSpace L] [IsTopologicalRing K] [IsTopologicalRing L]
    (e : K ≃+* L) (he : Continuous e) (hi : Continuous e.symm) (V : Type*)
    [TopologicalSpace V] : ULift.{u + 1} C(V, K) ≃+* ULift.{u + 1} C(V, L) :=
  ULift.ringEquiv.trans
    (({ e.toRingHom.compLeftContinuous V he with
      invFun := e.symm.toRingHom.compLeftContinuous V hi
      left_inv f := by
        ext x
        exact e.symm_apply_apply (f x)
      right_inv f := by
        ext x
        exact e.apply_symm_apply (f x) } : C(V, K) ≃+* C(V, L)).trans ULift.ringEquiv.symm)

/-- The condensed ring of continuous maps into `𝒪_E` is the one into `𝒪_{ULift E}`. -/
noncomputable def continuousMapRingSheafIntegralIso :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI := spectralNorm.normedField ℚ_[l] (ULift.{u} E)
    letI : TopologicalSpace (ULift.{u} E) :=
      (spectralNorm.normedField ℚ_[l] (ULift.{u} E)).toUniformSpace.toTopologicalSpace
    Profinite.continuousMapRingSheaf.{u} (Padic.coefficientExtensionIntegers l E) ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l (ULift.{u} E)) := by
  letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
  letI := spectralNorm.normedField ℚ_[l] (ULift.{u} E)
  letI : TopologicalSpace (ULift.{u} E) :=
    (spectralNorm.normedField ℚ_[l] (ULift.{u} E)).toUniformSpace.toTopologicalSpace
  have hi := isometry_uliftUp.{u} l E
  letI : PseudoEMetricSpace (ULift.{u} E) :=
    (spectralNorm.normedField ℚ_[l] (ULift.{u} E)).toPseudoMetricSpace.toPseudoEMetricSpace
  have hup : Continuous (ULift.up : E → ULift.{u} E) := hi.continuous
  have hdown : Continuous (ULift.down : ULift.{u} E → E) :=
    (hi.right_inv (g := ULift.down) fun _ ↦ rfl).continuous
  have he : Continuous (uliftIntegersRingEquiv.{u} l E) :=
    (hup.comp continuous_subtype_val).subtype_mk _
  have hs : Continuous (uliftIntegersRingEquiv.{u} l E).symm :=
    (hdown.comp continuous_subtype_val).subtype_mk _
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun S ↦
    (continuousMapULiftRingEquiv (uliftIntegersRingEquiv.{u} l E) he hs
      S.unop).toRingCatIso) fun _ ↦ rfl)

/-- The integral coefficient ring `DerivedNakayama.integerRingSheaf l E'` is the condensed ring of
continuous maps into `𝒪_{E'}` for the spectral-norm topology. -/
theorem integerRingSheaf_eq_continuousMapRingSheafOfUniverse (E' : Type u) [Field E']
    [Algebra ℚ_[l] E'] [FiniteDimensional ℚ_[l] E'] :
    DerivedNakayama.integerRingSheaf l E' =
      letI := spectralNorm.normedField ℚ_[l] E'
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E') := by
  have key (B : Type u) [Ring B] (t₁ t₂ : TopologicalSpace B) (ht : t₁ = t₂)
      (h₁ : @IsTopologicalRing B t₁ _) (h₂ : @IsTopologicalRing B t₂ _) :
      @Profinite.continuousCoefficientRingSheaf.{u} B t₁ _ h₁ =
        @Profinite.continuousMapRingSheafOfUniverse.{u, u} B t₂ _ h₂ := by
    subst t₂
    rfl
  apply key
  exact congrArg (fun t : TopologicalSpace E' ↦ TopologicalSpace.induced
    (fun x : Padic.coefficientExtensionIntegers l E' ↦ (x : E')) t)
    (DerivedNakayama.coefficientTopology l E').symm

/-- The condensed ring of continuous maps into `𝒪_E` is the integral coefficient ring
`DerivedNakayama.integerRing` of `ULift E`, as condensed abelian groups. -/
noncomputable def continuousMapRingObjIntegerRingIso :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E) ≅
      DerivedNakayama.integerRing l (ULift.{u} E) :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    (continuousMapRingSheafIntegralIso.{u} l E ≪≫
      eqToIso (integerRingSheaf_eq_continuousMapRingSheafOfUniverse l (ULift.{u} E)).symm)

instance isMonHom_continuousMapRingObjIntegerRingIso_hom :
    IsMonHom (continuousMapRingObjIntegerRingIso.{u} l E).hom :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) _

instance isMonHom_continuousMapRingObjIntegerRingIso_inv :
    IsMonHom (continuousMapRingObjIntegerRingIso.{u} l E).inv :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) _

end AlgebraicGeometry.ProEtale.IntegralQuotient
