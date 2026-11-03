/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-! # Admissibility of the spectral integral coefficient ring -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private def continuousCoefficientIso
    (A : Type u) (B : Type) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf.{u} B := by
  let q : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous _ he).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      inv := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous _ hi).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact e.symm_apply_apply (x.down z)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact e.apply_symm_apply (x.down z) }
  exact q

private theorem coefficientIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (DerivedNakayama.integerRing l E) ≅
        Mon.mk (Profinite.padicIntegersRingObj l F)) := by
  let f : E →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  let F : PadicAlgCl.FiniteIntermediateField l :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  let : FiniteDimensional ℚ_[l] F := F.property
  let e : E ≃ₐ[ℚ_[l]] F := f.equivFieldRange
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := PadicAlgCl.normedFieldOfAlgebra l F
  have hn (x : E) : Padic.coefficientExtensionAbsoluteValue l E x = ‖f x‖ := by
    let a : AbsoluteValue E ℝ :=
      { toFun := fun x ↦ ‖f x‖
        map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
        nonneg' := fun x ↦ norm_nonneg _
        eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
        add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
    have ha (y : ℚ_[l]) : a (algebraMap ℚ_[l] E y) = ‖y‖ := by
      change ‖f (algebraMap ℚ_[l] E y)‖ = ‖y‖
      rw [f.commutes]
      exact PadicAlgCl.norm_extends l y
    exact (spectralNorm_unique_field_norm_ext ha x).symm
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔
      e x ∈ PadicAlgCl.integers l F := by
    have h := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
    rw [hn] at h
    exact h.trans (by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
      rfl)
  let t : Padic.coefficientExtensionIntegers l E ≃+* PadicAlgCl.integers l F :=
    { toFun := fun x ↦ ⟨e x.val, (hm x.val).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, (hm _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  have ht : Isometry t := by
    apply AddMonoidHomClass.isometry_of_norm t
    intro x
    change ‖f x.val‖ = Padic.coefficientExtensionAbsoluteValue l E x.val
    exact (hn x.val).symm
  have hti : Continuous t.symm := (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  let q : DerivedNakayama.integerRingSheaf l E ≅
      Profinite.padicIntegersCondensedRing.{u} l F :=
    continuousCoefficientIso _ _ t ht.continuous hti
  let G := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (G.mapIso q).hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  exact ⟨F, ⟨Mon.mkIso' (G.mapIso q)⟩⟩

/-- The continuous spectral integer ring is an admissible integral coefficient.
Source: latest blueprint sec-smooth-purity/sk-lem-sp-tower/
thm-coef-integral-verdier.proof.md, integral dualizing input, and the coefficient
convention of sk-def-localizing-closure
(blueprint: lem-coef-integral-verdier-admissibility).

Proof: embed the finite extension into the fixed algebraic closure and take its
finite field range F. Uniqueness of the extending absolute value identifies the
spectral norm with the norm of this embedding. Restrict the field equivalence to
the two valuation rings. It is an isometry in both directions, hence induces an
isomorphism of the continuous condensed ring sheaves. Forget to abelian sheaves,
retain the monoid structure, and use the integral admissibility disjunct for F. -/
theorem integralVerdier_coefficient_admissible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsLocalizingAdmissibleCoefficient l (DerivedNakayama.integerRing l E) := by
  obtain ⟨F, e⟩ := coefficientIso l E
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, e⟩))))

private theorem quotient_killed (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  exact hkill

/-- Every positive spectral integer quotient is an admissible finite coefficient.
Source: the finite reductions in the first paragraph of the proof of
thm-coef-integral-verdier
(blueprint: lem-coef-integral-verdier-quotient-admissibility).
Proof: the quotient ideal is open by the uniformizer coset basis. The quotient
is finite and killed by an ell-power since ell belongs to the maximal ideal.
Shrink the carrier and transport its discrete topology and continuous sections
along the ring equivalence, obtaining the finite admissibility disjunct. -/
theorem integralVerdier_quotient_admissible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    IsLocalizingAdmissibleCoefficient l (DerivedNakayama.quotientRing l E (n + 1)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology A := finiteTopology_discrete l E n
  let B := Shrink.{0} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := inferInstance
  let e : A ≃+* B := (Shrink.ringEquiv.{0} A).symm
  let q : DerivedNakayama.quotientRingSheaf l E (n + 1) ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    continuousCoefficientIso A B e continuous_of_discreteTopology
      continuous_of_discreteTopology
  let G := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (G.mapIso q).hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  refine Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨n + 1, ?_⟩, ⟨Mon.mkIso' (G.mapIso q)⟩⟩
  intro b
  have hk : ((l ^ (n + 1) : ℕ) : B) = 0 := by
    calc
      ((l ^ (n + 1) : ℕ) : B) = e ((l ^ (n + 1) : ℕ) : A) :=
        (map_natCast e _).symm
      _ = 0 := (congrArg e (quotient_killed l E (n + 1))).trans e.map_zero
  simp only [nsmul_eq_mul, hk, zero_mul]

end AlgebraicGeometry.ProEtale
