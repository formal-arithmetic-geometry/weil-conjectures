/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
public import WeilConjectures.AlgebraicGeometry.Curve

/-!
# Coherent cohomology of the projective line and the canonical sheaf of a curve

Let `k` be a field and `ℙ¹_k = ProjectiveLine (Spec k)`. This file records the cohomology of the
twisting sheaves `𝒪(d)` on `ℙ¹_k`, the vanishing of the cohomology of quasi-coherent sheaves on
`ℙ¹_k` in degrees `≥ 2`, the finiteness of the cohomology of coherent sheaves on `ℙ¹_k`, and the
invertibility of the canonical sheaf `Ω¹_{C/k}` of a smooth curve.

The twisting sheaves are `AlgebraicGeometry.ProjectiveSpace.twist`, which exist and are
invertible by `AlgebraicGeometry.ProjectiveSpace.isInvertible_twist` (blueprint
`lem-sc-p1-twist-exists`). The cohomology of the twists on `ℙ¹_k` is the case `d = 1` of
Serre's computation of the cohomology of `ℙᵈ_k`, `sk-thm-picard-pn`.

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
- `AlgebraicGeometry.isInvertible_relativeDifferentials`: the canonical sheaf of a smooth curve
  is invertible.
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

lemma mem_twistSectionPairs (d : ℤ) (pq : k[X] × k[X]) :
    pq ∈ twistSectionPairs k d ↔ toLaurent pq.1 = T d * invert (toLaurent pq.2) := by
  simp [twistSectionPairs, sub_eq_zero]

/-- **Sections of the twists.** The global sections of `𝒪(d)` on `ℙ¹_k` are the pairs
`(p, q) ∈ k[t] × k[s]` with `p(t) = tᵈ q(1/t)` in `k[t, t⁻¹]`.

Only the existence of a `k`-linear isomorphism is asserted: the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist` is not constructed from the generating sections
`g₀, g₁` of the blueprint, so the isomorphism is not pinned down as "taking coefficients".

(blueprint: `lem-sc-p1-twist-sections`) -/
theorem nonempty_H_zero_twist_equiv_twistSectionPairs (d : ℤ) :
    Nonempty ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0 ≃ₗ[k]
      twistSectionPairs k d) :=
  sorry

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
    Subsingleton ((ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).H 0) :=
  sorry

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
  sorry

/-- **Vanishing above the dimension on `ℙ¹_k`.** For every quasi-coherent `𝒪_{ℙ¹_k}`-module `ℱ`,
`H^q(ℙ¹_k, ℱ) = 0` for all `q ≥ 2`: the Čech complex of the standard cover by the two affine
opens `U₀`, `U₁` computes the cohomology of `ℱ`, and has length two.

(blueprint: `lem-sc-p1-hi-vanishing`) -/
theorem subsingleton_H_of_two_le (ℱ : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) ℱ]
    {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) :=
  sorry

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
  sorry

end ProjectiveLine

/-- **The canonical sheaf of a smooth curve is a line bundle.** Let `C` be a smooth curve over
`k` of relative dimension one. Then `ω_C = Ω¹_{C/k}` is an invertible `𝒪_C`-module: locally
`C = Spec A` with `A` a smooth `k`-algebra of dimension one, and by the Jacobian criterion
`Ω_{A/k}` is projective of rank one.

(blueprint: `lem-sc-canonical-sheaf`) -/
theorem isInvertible_relativeDifferentials {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [SmoothOfRelativeDimension 1 f] :
    f.relativeDifferentials.IsInvertible :=
  sorry

/-- **Coherent cohomology of a smooth projective curve over an algebraically closed field.** Let
`k` be algebraically closed, `X` a smooth projective curve over `k` (an integral scheme of
dimension one, smooth over `k`, with a closed immersion `i` into some `ℙⁿ_k` over `k`), and `ℱ`
a coherent `𝒪_X`-module. Then `H⁰(X, ℱ)` and `H¹(X, ℱ)` are finite-dimensional over `k`, and
`H^q(X, ℱ) = 0` for `q ≥ 2`.

Choose a finite morphism `u : X ⟶ ℙ¹_k`; then `u_* ℱ` is coherent, `R^q u_* ℱ = 0` for `q > 0`
since `u` is affine, so `H^q(X, ℱ) ≅ H^q(ℙ¹_k, u_* ℱ)`, and
`AlgebraicGeometry.ProjectiveLine.finiteDimensional_H` and
`AlgebraicGeometry.ProjectiveLine.subsingleton_H_of_two_le` apply.

(blueprint: `lem-pc-curve-coherent-finiteness`) -/
theorem finiteDimensional_H_of_isCurve {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsIntegral X] [IsCurve (X ↘ Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] (hX : topologicalKrullDim X = 1) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k)) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    FiniteDimensional k (ℱ.H 0) ∧ FiniteDimensional k (ℱ.H 1) ∧
      ∀ q, 2 ≤ q → Subsingleton (ℱ.H q) :=
  sorry

end AlgebraicGeometry
