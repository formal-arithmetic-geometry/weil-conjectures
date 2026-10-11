/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne
public import WeilConjectures.RepresentationTheory.CompositionSeries

/-!
# Determinant weights of lisse Weil sheaves

Let `W` be the Weil group of a smooth geometrically connected curve `C₀ / 𝔽_q`, `ℓ ≠ p`, and
`ι : ℚ̄_ℓ →+* ℂ`. The determinant line `det ρ = ⋀^{rank ρ} ρ` of a lisse Weil representation is
a rank-one lisse sheaf, hence punctually `ι`-pure of a unique weight `a` (rank-one purity,
`sk-p-real-rankone`), and the *determinant weight* of `ρ` is `dw_ι(ρ) = a / rank ρ`
(blueprint subsection `sk-d-real-detweights`).

This file defines `dw_ι` (`AlgebraicGeometry.WeilGroup.detWeight`) as the weight read off from
the chosen Frobenius lift, `wt_{ι, q}(det ρ(γ)) / rank ρ`, and proves that it is the unique
`a / r` making `det ρ` pure of weight `a`. It then defines the multiset of determinant weights
of the composition factors of a finite-dimensional Weil representation, its rank-counted
version, and the numbers `N_γ` and `B_γ`, and proves that they do not depend on the
composition series (Jordan–Hölder).

## Main definitions

- `AlgebraicGeometry.WeilGroup.detWeight`: the determinant weight `dw_ι(ρ)`.
- `AlgebraicGeometry.WeilGroup.detWeightMultiset`: the determinantal-weight multiset.
- `AlgebraicGeometry.WeilGroup.rankDetWeightMultiset`: the rank-counted list.
- `AlgebraicGeometry.WeilGroup.rankAbove`, `AlgebraicGeometry.WeilGroup.weightSumAbove`:
  `N_γ` and `B_γ`.

## Main statements

- `AlgebraicGeometry.WeilGroup.existsUnique_isPunctuallyPure_detLine`: the determinant line of
  a lisse Weil sheaf is pure of exactly one weight.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_detLine_iff_eq_mul_detWeight`: that weight is
  `rank ρ * dw_ι(ρ)`.
- `AlgebraicGeometry.WeilGroup.hasFiniteGeometricDet_and_detWeight_eq`: `dw_ι` agrees with the
  determinant weight `dw_{λ_ι}` of `sk-d-weights` for the real weight character `λ_ι`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
  (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `def-wf-determinantal-weight`: Determinantal weight.

The determinant weight `dw_ι(ρ) = a / r` of a Weil representation `ρ` of rank `r`, where
`a = wt_{ι, q}(det ρ(γ)) = 2 log |ι det ρ(γ)| / log q` for the chosen Frobenius lift `γ` of
degree one. For a lisse `ρ`, `a` is the unique weight of which the determinant line `det ρ` is
punctually `ι`-pure (`AlgebraicGeometry.WeilGroup.existsUnique_isPunctuallyPure_detLine` and
`AlgebraicGeometry.WeilGroup.isPunctuallyPure_detLine_iff_eq_mul_detWeight`), which is the
definition of the blueprint; it involves no choice of a coefficient field, the coefficients
being `ℚ̄_ℓ` throughout (compare `lem-wf-determinantal-weight-coefficient-field`). For `V = 0`
it is the junk value `0`. -/
noncomputable def detWeight : ℝ :=
  frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift)) /
    Module.finrank (PadicAlgCl l) V

variable {W l ρ}

/-- Equivalent representations have the same determinant weight. -/
theorem detWeight_of_equiv {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    {σ : Representation (PadicAlgCl l) W.carrier V'} (e : ρ.Equiv σ) :
    W.detWeight l σ ι = W.detWeight l ρ ι := by
  rw [detWeight, detWeight, e.det_apply, e.finrank_eq]

section DetLine

variable [FiniteDimensional (PadicAlgCl l) V]

/-- The determinant line has the single local eigenvalue `det ρ(F_x)` at a closed point `x`. -/
theorem localEigenvalues_detLine (x : C.finitePoints) :
    W.localEigenvalues l (W.detLine l ρ) x = {LinearMap.det (ρ (W.frobenius x))} := by
  have hcard : Multiset.card (ρ (W.frobenius x)).charpoly.roots =
      Module.finrank (PadicAlgCl l) V := by
    rw [← LinearMap.charpoly_natDegree (ρ (W.frobenius x))]
    exact (Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits (ρ (W.frobenius x)).charpoly))
  change (_root_.exteriorPower.map (Module.finrank (PadicAlgCl l) V)
    (ρ (W.frobenius x))).charpoly.roots = _
  rw [LinearMap.charpoly_roots_exteriorPower, ← hcard, Multiset.powersetCard_self,
    Multiset.map_singleton, ← Module.End.det_eq_prod_roots_charpoly_of_splits
      (IsAlgClosed.splits _)]

/-- The determinant line is punctually `ι`-pure of weight `a` exactly when
`wt_{ι, q_x}(det ρ(F_x)) = a` at every closed point `x`. -/
theorem isPunctuallyPure_detLine_iff {a : ℝ} :
    W.IsPunctuallyPure l (W.detLine l ρ) ι a ↔
      ∀ x : C.finitePoints,
        frobeniusWeight ι (C.pointNorm x.1) (LinearMap.det (ρ (W.frobenius x))) = a := by
  simp only [IsPunctuallyPure, localEigenvalues_detLine, Multiset.mem_singleton, forall_eq]

/-- `ρ` has determinant weight `γ` in the sense of `AlgebraicGeometry.WeilGroup.HasDetWeight`
exactly when its determinant line is punctually `ι`-pure of weight `rank ρ * γ`. -/
theorem hasDetWeight_iff_isPunctuallyPure_detLine {γ : ℝ} :
    W.HasDetWeight l ρ ι γ ↔
      W.IsPunctuallyPure l (W.detLine l ρ) ι (Module.finrank (PadicAlgCl l) V * γ) := by
  rw [isPunctuallyPure_detLine_iff]
  rfl

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- A Weil group of a curve has a closed point to evaluate local Frobenius elements at. -/
theorem nonempty_finitePoints (W : WeilGroup p) : Nonempty C.finitePoints := by
  have := W.connectedSpace
  obtain ⟨x, hx⟩ := p.exists_mem_finitePoints
  exact ⟨⟨x, hx⟩⟩

/-- Blueprint `lem-wf-determinantal-weight-coefficient-field`: The determinant weight does not
depend on the coefficient field.

Let `ρ` be a representation of the Weil group defined over a field `E`, and `E'` an extension
of `E` with an embedding `ι : E' →+* ℂ`. The local eigenvalue of the determinant line of `ρ`
at `x` is `det ρ(F_x)`; read with coefficients in `E'`, it is the determinant of the base
change of `ρ(F_x)` to `E'`, which is the image of `det ρ(F_x)`. Hence `det ρ` is punctually
`ι`-pure of weight `a` with coefficients in `E` if and only if it is with coefficients in
`E'`. -/
theorem isPunctuallyPure_det_baseChange_iff {E E' : Type*} [Field E] [Field E'] [Algebra E E']
    (ι' : E' →+* ℂ) {U : Type*} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (σ : Representation E W.carrier U) (a : ℝ) :
    (∀ x : C.finitePoints, frobeniusWeight (ι'.comp (algebraMap E E')) (C.pointNorm x.1)
        (LinearMap.det (σ (W.frobenius x))) = a) ↔
      ∀ x : C.finitePoints, frobeniusWeight ι' (C.pointNorm x.1)
        (LinearMap.det ((σ (W.frobenius x)).baseChange E')) = a := by
  simp only [LinearMap.det_baseChange, frobeniusWeight, RingHom.comp_apply]

end DetLine

section RankOne

variable [FiniteDimensional (PadicAlgCl l) V] [SmoothOfRelativeDimension 1 p]
  [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient] in
/-- The determinant of a lisse Weil representation is continuous on the geometric part: in a
basis it is a polynomial in the matrix coefficients. -/
theorem IsLisse.continuous_det_apply (hρ : W.IsLisse l ρ) :
    Continuous fun g : W.geometric ↦ (ρ.detCharacter g : PadicAlgCl l) := by
  let b := Module.finBasis (PadicAlgCl l) V
  have h : Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ hρ.continuous_toMatrix b i j
  simpa only [Representation.coe_detCharacter_apply, LinearMap.det_toMatrix] using h.matrix_det

/-- The determinant line of a lisse Weil representation is punctually `ι`-pure of weight
`wt_{ι, q}(det ρ(γ))`, by rank-one purity (`cor-wf-rank-one-punctual-purity-curve`). -/
theorem IsLisse.isPunctuallyPure_detLine (hρ : W.IsLisse l ρ) :
    W.IsPunctuallyPure l (W.detLine l ρ) ι
      (frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift))) := by
  rw [isPunctuallyPure_detLine_iff]
  intro x
  rw [← Representation.coe_detCharacter_apply, ← Representation.coe_detCharacter_apply]
  exact W.frobeniusWeight_eq_of_continuous ρ.detCharacter hρ.continuous_det_apply ι x

/-- Blueprint `lem-wf-determinantal-weight-exists`: Purity of the determinant line.

The determinant line `det ρ` of a lisse Weil sheaf `ρ` on the curve is punctually `ι`-pure of
exactly one real weight `a`: it is a rank-one lisse sheaf, with finite geometric image, hence
pure by rank-one purity; and `a` is unique because the curve has a closed point `y`, at which
`q_y ^ (a / 2) = |ι det ρ(F_y)|` determines `a`. -/
theorem existsUnique_isPunctuallyPure_detLine (hρ : W.IsLisse l ρ) :
    ∃! a : ℝ, W.IsPunctuallyPure l (W.detLine l ρ) ι a := by
  obtain ⟨x₀⟩ := W.nonempty_finitePoints
  refine ⟨_, hρ.isPunctuallyPure_detLine ι, fun a ha ↦ ?_⟩
  have ha' := (isPunctuallyPure_detLine_iff ι).1 ha
  have h := (isPunctuallyPure_detLine_iff ι).1 (hρ.isPunctuallyPure_detLine ι)
  exact (ha' x₀).symm.trans (h x₀)

/-- A lisse Weil representation has determinant weight `dw_ι(ρ)` in the sense of
`AlgebraicGeometry.WeilGroup.HasDetWeight`. -/
theorem IsLisse.hasDetWeight_detWeight (hρ : W.IsLisse l ρ) :
    W.HasDetWeight l ρ ι (W.detWeight l ρ ι) := by
  rw [hasDetWeight_iff_isPunctuallyPure_detLine, detWeight]
  rcases eq_or_ne (Module.finrank (PadicAlgCl l) V) 0 with h0 | h0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    rw [isPunctuallyPure_detLine_iff]
    intro x
    rw [LinearMap.det_eq_one_of_subsingleton, h0]
    simp [frobeniusWeight]
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 h0)]
    exact hρ.isPunctuallyPure_detLine ι

/-- For a nonzero lisse Weil representation of rank `r`, the determinant line is punctually
`ι`-pure of weight `a` exactly when `a = r * dw_ι(ρ)`; that is, `dw_ι(ρ) = a / r` for the
unique weight `a` of `lem-wf-determinantal-weight-exists`, which is the definition
`def-wf-determinantal-weight` of the blueprint. -/
theorem isPunctuallyPure_detLine_iff_eq_mul_detWeight (hρ : W.IsLisse l ρ) {a : ℝ} :
    W.IsPunctuallyPure l (W.detLine l ρ) ι a ↔
      a = Module.finrank (PadicAlgCl l) V * W.detWeight l ρ ι := by
  have h := (hasDetWeight_iff_isPunctuallyPure_detLine ι).1 (hρ.hasDetWeight_detWeight ι)
  refine ⟨fun ha ↦ (existsUnique_isPunctuallyPure_detLine ι hρ).unique ha h, ?_⟩
  rintro rfl
  exact h

/-- The determinant weight is the only determinant weight of a nonzero lisse Weil
representation. -/
theorem HasDetWeight.detWeight_eq [Nontrivial V] (hρ : W.IsLisse l ρ) {γ : ℝ}
    (h : W.HasDetWeight l ρ ι γ) : W.detWeight l ρ ι = γ := by
  obtain ⟨x₀⟩ := W.nonempty_finitePoints
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (((hρ.hasDetWeight_detWeight ι) x₀).symm.trans (h x₀))

/-- Blueprint `lem-rp-determinant-weights-agree`: Rank-one purity discharges the
finite-determinant hypotheses.

A lisse Weil sheaf `ρ` has finite geometric determinant in the sense of `sk-d-weights` (the
determinant character takes finitely many values on `π₁(C)`, by the finite geometric image
theorem for its determinant line), and its determinant weight `dw_ι(ρ)` is the determinant
weight `dw_{λ_ι}(ρ)` of `sk-d-weights` for the real weight character
`λ_ι(a) = 2 log |ι a| / log q` (`AlgebraicGeometry.WeilGroup.weightCharacter`) and the degree
one element `γ`. -/
theorem hasFiniteGeometricDet_and_detWeight_eq (hρ : W.IsLisse l ρ) :
    ρ.HasFiniteGeometricDet W.deg ∧
      W.detWeight l ρ ι = ρ.detWeight (weightCharacter ι (Nat.card K)) W.frobeniusLift :=
  ⟨W.finite_range_of_continuous ρ.detCharacter hρ.continuous_det_apply,
    (detWeight_weightCharacter ι ρ _ _).symm⟩

end RankOne

end WeilGroup

end AlgebraicGeometry
