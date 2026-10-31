/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.FourierTransform.FiniteFieldAffineVanishing
import WeilConjectures.Algebra.LocalCharacterOrthogonality
import WeilConjectures.EtaleCohomology.TateTwist.Normalized
import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
import Mathlib.FieldTheory.Finite.Basic

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.Etale

/-- Affine compact-support vanishing interface for a nontrivial finite-level
Artin--Schreier linear form. The explicit nontriviality hypothesis is needed to
exclude the constant-character case.
Source: latest blueprint, `lem-fd-character-integral-finite`, proof Steps 2--8.

Proof: the positive-level coefficient quotient is local. For a nontrivial character into
this ring, its normalized character sum is an idempotent; locality and nontriviality force
that sum to vanish. Apply finite-field Artin--Schreier affine-line vanishing, base change
it to the space of the remaining coordinates, and use a nonzero coefficient to make the
linear form the line coordinate. Compact-support base change and composition give zero.
(blueprint: lem-fd-character-integral-finite-affine-core) -/
theorem finite_character_integral_affine_core
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    [Invertible (Fintype.card k₀ : Padic.coefficientExtensionRing ell E n)]
    (ψ : AddChar k₀ (Padic.coefficientExtensionRing ell E n)ˣ)
    (hψ : ψ ≠ 1)
    (Ω : Type u) [Field Ω] [Algebra k₀ Ω] [IsAlgClosed Ω]
    (r : ℕ) (_hr : 1 ≤ r) (c : Fin r → Ω) (hc : c ≠ 0)
    [HasCompactification (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω)) ↘
      Spec (CommRingCat.of Ω))]
    (F : Sheaf (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω))).smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)))
    (hF : F =
      let A := Padic.coefficientExtensionRing ell E n
      let X := 𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω))
      letI : X.Over (Spec (.of k₀)) :=
        ⟨X ↘ Spec (.of Ω) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ Ω))⟩
      artinSchreierSheafOf X
        (MonoidHom.compAddChar (Units.coeHom A) ψ)
        (∑ i : ULift.{u} (Fin r),
          AffineSpace.coord (Spec (.of Ω)) i *
            (X ↘ Spec (.of Ω)).appTop
              ((Scheme.ΓSpecIso (.of Ω)).inv.hom (c i.down)))) :
    IsZero ((R(𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω)) ↘
      Spec (CommRingCat.of Ω))_![ModuleCat.{u + 1}
        (Padic.coefficientExtensionRing ell E n)]).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  classical
  have _ := hpell
  let A := Padic.coefficientExtensionRing ell E n
  have : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  have : IsLocalRing A := by
    let R := Padic.coefficientExtensionIntegers ell E
    have h := (Padic.extension_integers_dvr ell E
      (Padic.coefficientExtensionAbsoluteValue ell E)
      (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
    have : IsLocalRing R := h.2.2.2.1
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} : Set R) =
        Padic.coefficientExtensionMaximalIdeal ell E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hproper : Padic.coefficientExtensionIdeal ell E n ≠ ⊤ := by
      apply ne_top_of_le_ne_top h.2.2.2.2.1.ne_top
      exact (Ideal.pow_le_self (by omega : n ≠ 0)).trans_eq hgen
    have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hproper
    exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : NeZero (ringChar A) := ⟨CharP.char_ne_zero_of_finite A _⟩
  let : HasTateTwist A := inferInstance
  have : HasTateTwist.IsNormalized A := inferInstance
  have hu : IsUnit (p : A) := by
    obtain ⟨m, hm, hcard⟩ := FiniteField.card (K := k₀) p
    apply (isUnit_pow_iff m.ne_zero).mp
    rw [← Nat.cast_pow, ← hcard]
    exact isUnit_of_invertible _
  let : Invertible (p : A) := hu.invertible
  have : HasInvertibleExponent A (Spec (.of k₀)) :=
    HasInvertibleExponent.spec_of_charP A p
  let Ψ : AddChar k₀ A := MonoidHom.compAddChar (Units.coeHom A) ψ
  have hΨ : Ψ ≠ 1 := by
    intro h
    apply hψ
    ext b
    exact congrArg (fun χ : AddChar k₀ A ↦ χ b) h
  have hsum := AddChar.sum_eq_zero_of_ne_one_of_isLocalRing Ψ hΨ
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  let d : ULift.{u} (Fin r) → Γ(Spec (.of Ω), ⊤) :=
    fun j ↦ (Scheme.ΓSpecIso (.of Ω)).inv.hom (c j.down)
  have hd : IsUnit (d ⟨i⟩) := (isUnit_iff_ne_zero.mpr hi).map
    (Scheme.ΓSpecIso (.of Ω)).inv.hom
  rw [hF]
  exact isZero_rightDerivedLowerShriek_finiteField_linearForm A (Spec (.of Ω))
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ Ω))) d ⟨i⟩ hd Ψ hsum

end AlgebraicGeometry.Etale
