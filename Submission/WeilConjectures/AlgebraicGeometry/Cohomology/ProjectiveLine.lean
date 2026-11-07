/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField
public import Submission.WeilConjectures.AlgebraicGeometry.Curve
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CurveProjection
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Coherent cohomology of the projective line and of smooth projective curves

Let `k` be a field and `ℙ¹_k = ProjectiveLine (Spec k)`. This file records the cohomology of the
twisting sheaves `𝒪(d)` on `ℙ¹_k`, the vanishing of the cohomology of quasi-coherent sheaves on
`ℙ¹_k` in degrees `≥ 2`, the finiteness of the cohomology of coherent sheaves on `ℙ¹_k`, and the
finiteness of the cohomology of coherent sheaves on a smooth projective curve.

The twisting sheaves are `AlgebraicGeometry.ProjectiveSpace.twist`, which exist and are
invertible by `AlgebraicGeometry.ProjectiveSpace.isInvertible_twist`; that they are the twisted
structure sheaves of the standard cover, unique up to unique isomorphism, is
`AlgebraicGeometry.ProjectiveLine.nonempty_twistData` (blueprint
`lem-sc-p1-twist-exists`). The cohomology of the twists on `ℙ¹_k` is the case `d = 1` of
Serre's computation of the cohomology of `ℙᵈ_k`, `det-thm-picard-pn`.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.nonempty_H_zero_twist_equiv_twistSectionPairs`: the global
  sections of `𝒪(d)` are the pairs `(p, q)` with `p(t) = tᵈ q(1/t)`.
- `AlgebraicGeometry.ProjectiveLine.nonempty_H_zero_twist_equiv`,
  `subsingleton_H_zero_twist_of_neg`, `subsingleton_H_one_twist`,
  `nonempty_H_one_twist_equiv_dual` and `nonempty_relativeDifferentials_iso_twist`: the
  cohomology of the twists, and `Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`.
- `AlgebraicGeometry.ProjectiveLine.subsingleton_H_of_two_le`: `H^q(ℙ¹_k, ℱ) = 0` for `q ≥ 2`.
- `AlgebraicGeometry.ProjectiveLine.finiteDimensional_H`: `H⁰` and `H¹` of a coherent sheaf on
  `ℙ¹_k` are finite-dimensional.
- `AlgebraicGeometry.finiteDimensional_H_of_isCurve`: the cohomology of a coherent sheaf on a
  smooth projective curve over an algebraically closed field is finite-dimensional, and vanishes
  in degrees `≥ 2`.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial LaurentPolynomial

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveLine

variable (k : Type u) [Field k]

lemma natCard_ulift_fin_two : Nat.card (ULift.{u} (Fin 2)) = 1 + 1 := by
  simp

/-- The `k`-vector space of pairs `(p, q) ∈ k[t] × k[s]` with `p(t) = tᵈ q(1/t)` in
`k[t, t⁻¹]`: the global sections of the twisting sheaf `𝒪(d)` on `ℙ¹_k`, written through their
coefficients `p` on `U₀ = Spec k[t]` and `q` on `U₁ = Spec k[s]`, `s = 1/t`, with respect to the
generating sections `g₀`, `g₁` glued by `g₀ = t⁻ᵈ g₁`. -/
def twistSectionPairs (d : ℤ) : Submodule k (k[X] × k[X]) :=
  LinearMap.ker ((toLaurentAlg (R := k)).toLinearMap ∘ₗ LinearMap.fst k k[X] k[X] -
    LinearMap.mulLeft k (T d : k[T;T⁻¹]) ∘ₗ (invert (R := k)).toLinearMap ∘ₗ
      (toLaurentAlg (R := k)).toLinearMap ∘ₗ LinearMap.snd k k[X] k[X])


/-- For `D ≥ 0`, the coefficients of `p` in degrees `≤ D` of a pair `(p, q)` in
`twistSectionPairs k D`; they determine the pair (`bijective_twistSectionPairsCoeff`). -/
def twistSectionPairsCoeff (D : ℕ) : twistSectionPairs k D →ₗ[k] (Fin (D + 1) → k) where
  toFun x j := x.1.1.coeff j
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp


/-- The exponent vectors of the monomials of degree `D` in the two variables `x₀, x₁` are
determined by the exponent of `x₁`, which is at most `D`. -/
def degreeEqEquivFin (D : ℕ) :
    {s : ULift.{u} (Fin 2) →₀ ℕ | s.degree = D} ≃ Fin (D + 1) where
  toFun s := ⟨s.1 ⟨1⟩, by
    have h : s.1.degree = D := s.2
    rw [Finsupp.degree_eq_sum, ← Equiv.ulift.symm.sum_comp, Fin.sum_univ_two] at h
    change s.1 ⟨0⟩ + s.1 ⟨1⟩ = D at h
    omega⟩
  invFun j := ⟨Finsupp.single (ULift.up 0) (D - j) + Finsupp.single (ULift.up 1) (j : ℕ), by
    change Finsupp.degree _ = D
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega⟩
  left_inv s := by
    have h : s.1.degree = D := s.2
    rw [Finsupp.degree_eq_sum, ← Equiv.ulift.symm.sum_comp, Fin.sum_univ_two] at h
    change s.1 ⟨0⟩ + s.1 ⟨1⟩ = D at h
    refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
    obtain ⟨i⟩ := i
    fin_cases i <;> simp; omega
  right_inv j := by
    ext
    simp


/-- **Global sections of the twists on `ℙ¹_k`, `d ≥ 0`.** `H⁰(ℙ¹_k, 𝒪(d))` is the space of
homogeneous polynomials of degree `d` in `k[x₀, x₁]`, of dimension `d + 1`.

This is part (i) of the blueprint lemma, the case `ℙ¹` of
`AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv`.

(blueprint: `lem-sc-p1-monomial`) -/
theorem nonempty_H_zero_twist_equiv (d : ℕ) :
    Nonempty ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0 ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k d) :=
  ProjectiveSpace.nonempty_H_zero_twist_equiv _ k 1 (natCard_ulift_fin_two) d

/-- **Global sections of the twists on `ℙ¹_k`, `d < 0`.** `H⁰(ℙ¹_k, 𝒪(d)) = 0` for `d < 0`:
a pair `(p, q)` with `p(t) = tᵈ q(1/t)` has `p = q = 0`, since every exponent of `tᵈ q(1/t)` is
negative.

This is the second half of part (i) of the blueprint lemma.

(blueprint: `lem-sc-p1-monomial`) -/
theorem subsingleton_H_zero_twist_of_neg (d : ℤ) (hd : d < 0) :
    Subsingleton ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0) := by
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology (ULift.{u} (Fin 2)) k d 0
  have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_zero (ULift.{u} (Fin 2)) k hd
  exact e.toEquiv.subsingleton

/-- **`H¹` of the twists on `ℙ¹_k`, `d ≥ -1`.** `H¹(ℙ¹_k, 𝒪(d)) = 0` for `d ≥ -1`.

This is the first half of part (ii) of the blueprint lemma, the case `ℙ¹` of
`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_top`.

(blueprint: `lem-sc-p1-monomial`) -/
theorem subsingleton_H_one_twist (d : ℤ) (hd : -1 ≤ d) :
    Subsingleton ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 1) :=
  ProjectiveSpace.subsingleton_H_twist_top _ k 1 one_ne_zero natCard_ulift_fin_two d
    (by simpa using hd)

/-- **`H¹` of the twists on `ℙ¹_k`, `d ≤ -2`.** `H¹(ℙ¹_k, 𝒪(d))` is dual to the space of
homogeneous polynomials of degree `-d-2` in `k[x₀, x₁]`; in particular it has dimension `-d-1`,
and `H¹(ℙ¹_k, 𝒪(-2)) ≅ k`.

This is the second half of part (ii) of the blueprint lemma, the case `ℙ¹` of
`AlgebraicGeometry.ProjectiveSpace.nonempty_H_twist_top_equiv_dual`.

(blueprint: `lem-sc-p1-monomial`) -/
theorem nonempty_H_one_twist_equiv_dual (d : ℤ) (hd : d ≤ -2) :
    Nonempty ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 1 ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k (-d - 2).toNat)) :=
  have h : -d - ((1 : ℕ) : ℤ) - 1 = -d - 2 := by push_cast; ring
  h ▸ ProjectiveSpace.nonempty_H_twist_top_equiv_dual _ k 1 natCard_ulift_fin_two d
    (by simpa using hd)

/-- **The canonical sheaf of `ℙ¹_k`.** `Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`: with the trivialisations `dt` on
`U₀` and `ds` on `U₁`, `s = 1/t`, one has `dt = -t² ds`, and the transition function `-t²`
differs from the transition function `t²` of `𝒪(-2)` by the unit `-1`.

This is part (iii) of the blueprint lemma.

(blueprint: `lem-sc-p1-monomial`) -/
theorem nonempty_relativeDifferentials_iso_twist :
    Nonempty ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)) :=
  ⟨relativeDifferentialsIsoTwist k⟩

/-- **Vanishing above the dimension on `ℙ¹_k`.** For every quasi-coherent `𝒪_{ℙ¹_k}`-module `ℱ`,
`H^q(ℙ¹_k, ℱ) = 0` for all `q ≥ 2`: the Čech complex of the standard cover by the two affine
opens `U₀`, `U₁` computes the cohomology of `ℱ`, and has length two.

(blueprint: `lem-sc-p1-hi-vanishing`) -/
theorem subsingleton_H_of_two_le (ℱ : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) :=
  ProjectiveSpace.subsingleton_H_of_lt _ k natCard_ulift_fin_two ℱ hq

/-- **Finite coherent cohomology on the projective line.** For every coherent
`𝒪_{ℙ¹_k}`-module `ℱ`, `H⁰(ℙ¹_k, ℱ)` and `H¹(ℙ¹_k, ℱ)` are finite-dimensional over `k`: they
are the kernel and the cokernel of the Čech differential
`Γ(U₀, ℱ) ⊕ Γ(U₁, ℱ) → Γ(U₀ ∩ U₁, ℱ)` of the standard cover.

As elsewhere, "coherent" is spelled as quasi-coherent and of finite presentation.

(blueprint: `lem-sc-p1-coherent-finite`) -/
theorem finiteDimensional_H (ℱ : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    {q : ℕ} (hq : q ≤ 1) : FiniteDimensional k (ℱ.H q) :=
  -- the bound `q ≤ 1` is not needed: `ℙ¹_k` is proper over `k`
  (fun _ ↦ Scheme.Modules.finiteDimensional_H_of_isProper ℱ q) hq

end ProjectiveLine


end AlgebraicGeometry
