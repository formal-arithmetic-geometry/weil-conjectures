/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Frobenius modules and their weights

A *Frobenius module* over a field `K` is a finite-dimensional `K`-vector space together with a
distinguished automorphism, the geometric Frobenius. It is the linear-algebra shadow of every
cohomological construction of the Weil conjectures: the stalk of an `ℓ`-adic sheaf at a closed
point with its local Frobenius, or a compactly supported cohomology group with the global
geometric Frobenius.

Fix a prime power `q` and an embedding `ι : K →+* ℂ`. A Frobenius module is *`ι`-pure of weight
`w` relative to `q`* if every eigenvalue `α` of its Frobenius satisfies `|ι α| = q ^ (w / 2)`,
and *has weights at most `w`* if `|ι α| ≤ q ^ (w / 2)`. The two cardinalities that occur in
practice are the residue cardinality `q_x` at a closed point and the cardinality `q` of the base
field; `FrobeniusModule.IsPureOfWeightOver` names the second one so that the convention is
visible at the use site.

This is the eigenvalue form of `Polynomial.IsPureOfWeight` of
`WeilConjectures.ZetaLinearAlgebra.Weights`, which says the same thing about the roots of the
reversed characteristic polynomial, for an integral weight and with the normalization
`‖z‖ = q ^ (-w / 2)` on the roots rather than on their reciprocals.

## Main declarations

- `FrobeniusModule`: the structure, with `FrobeniusModule.frobeniusEnd` the Frobenius as an
  endomorphism and `FrobeniusModule.Equiv` the isomorphisms.
- `FrobeniusModule.IsPureOfWeight`, `FrobeniusModule.HasWeightsAtMost` and their
  `…Over k` variants, the weight conditions relative to `q` and to `#k`.
- `FrobeniusModule.localPolynomial`: the polynomial `det (1 - T F)`, and
  `FrobeniusModule.IsReal`, the condition that its image under `ι : K →+* ℂ` has real
  coefficients.
- `FrobeniusModule.tateTwist`: the Tate twist `M(n)`, rescaling the Frobenius by `q ^ (-n)`.
- `FrobeniusModule.dual`: the dual `M^∨` with the inverse transpose of the Frobenius.
- `FrobeniusModule.IsPureOfWeight.tateTwist`: the twist by `n` lowers the weight by `2 n`.
- `FrobeniusModule.trivial`: the trivial Frobenius module `K`, and
  `FrobeniusModule.localPolynomial_eq_and_finrank_eq_of_equiv_tateTwist`: a Frobenius module
  isomorphic to `K(-d)` is one-dimensional with local polynomial `1 - qᵈ T`.
-/

@[expose] public section

universe u v

/-- A *Frobenius module* over a field `K`: a finite-dimensional `K`-vector space together with
an automorphism, the geometric Frobenius. -/
structure FrobeniusModule.{w, x} (K : Type x) [Field K] : Type (max x (w + 1)) where
  /-- The underlying `K`-vector space. -/
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  /-- The geometric Frobenius automorphism. -/
  frobenius : carrier ≃ₗ[K] carrier

namespace FrobeniusModule

attribute [instance] addCommGroup module finiteDimensional

variable {K : Type v} [Field K]

/-- The geometric Frobenius of a Frobenius module, as an endomorphism. -/
noncomputable def frobeniusEnd (M : FrobeniusModule.{u, v} K) :
    Module.End K M.carrier :=
  M.frobenius.toLinearMap

/-- An isomorphism of Frobenius modules: a `K`-linear isomorphism intertwining the two
Frobenius automorphisms. -/
structure Equiv (M N : FrobeniusModule.{u, v} K) where
  /-- The underlying `K`-linear isomorphism. -/
  toLinearEquiv : M.carrier ≃ₗ[K] N.carrier
  /-- The isomorphism intertwines the two Frobenius automorphisms. -/
  map_frobenius (x : M.carrier) :
    toLinearEquiv (M.frobenius x) = N.frobenius (toLinearEquiv x)

/-- `M` is *`ι`-pure of weight `w` relative to `q`* if every eigenvalue `α` of its geometric
Frobenius satisfies `|ι α| = q ^ (w / 2)`. -/
def IsPureOfWeight (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K) (w : ℝ) : Prop :=
  ∀ α : K, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ = (q : ℝ) ^ (w / 2)

/-- `M` *has weights at most `w` relative to `q`* if every eigenvalue `α` of its geometric
Frobenius satisfies `|ι α| ≤ q ^ (w / 2)`. -/
def HasWeightsAtMost (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K) (w : ℝ) : Prop :=
  ∀ α : K, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ ≤ (q : ℝ) ^ (w / 2)

/-- A module pure of weight `w` has weights at most `w`. -/
theorem IsPureOfWeight.hasWeightsAtMost {ι : K →+* ℂ} {q : ℕ} {M : FrobeniusModule.{u, v} K}
    {w : ℝ} (h : M.IsPureOfWeight ι q w) : M.HasWeightsAtMost ι q w :=
  fun α hα ↦ (h α hα).le

/-- For `q ≥ 1`, weights at most `w` are weights at most any `w' ≥ w`. -/
theorem HasWeightsAtMost.mono {ι : K →+* ℂ} {q : ℕ} (hq : 1 ≤ q)
    {M : FrobeniusModule.{u, v} K} {w w' : ℝ} (h : M.HasWeightsAtMost ι q w) (hww' : w ≤ w') :
    M.HasWeightsAtMost ι q w' :=
  fun α hα ↦ (h α hα).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) (by linarith))

/-- An isomorphism of Frobenius modules preserves the eigenvalues of the Frobenius. -/
theorem Equiv.hasEigenvalue {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) : N.frobeniusEnd.HasEigenvalue α := by
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.toLinearEquiv x) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · change N.frobenius (e.toLinearEquiv x) = α • e.toLinearEquiv x
    rw [← e.map_frobenius, ← map_smul]
    exact congrArg e.toLinearEquiv hx.1
  · exact (map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.2

/-- A Frobenius module isomorphic to one with weights at most `w` has weights at most `w`. -/
theorem HasWeightsAtMost.of_equiv {ι : K →+* ℂ} {q : ℕ} {M N : FrobeniusModule.{u, v} K}
    (e : M.Equiv N) {w : ℝ} (h : N.HasWeightsAtMost ι q w) : M.HasWeightsAtMost ι q w :=
  fun α hα ↦ h α (e.hasEigenvalue hα)

/-- The local polynomial `det (1 - T F)` of a Frobenius module, the reverse characteristic
polynomial of its Frobenius `F`. -/
noncomputable def localPolynomial (M : FrobeniusModule.{u, v} K) : Polynomial K :=
  M.frobeniusEnd.charpolyRev

/-- `M` is `ι`-*real* if the image under `ι` of its local polynomial `det (1 - T F)` has real
coefficients; equivalently, if the multiset of complex eigenvalues of `F` is stable under
complex conjugation. -/
def IsReal (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K) : Prop :=
  ∀ n : ℕ, (starRingEnd ℂ) (ι (M.localPolynomial.coeff n)) = ι (M.localPolynomial.coeff n)

/-- `M` is `ι`-pure of weight `w` *over the field `k`*: purity relative to `q = #k`. This is
the convention for the geometric Frobenius acting on the cohomology of a `k`-scheme, as opposed
to the Frobenius acting on a stalk, whose weights are taken relative to the residue cardinality
`q_x` at the point. -/
def IsPureOfWeightOver (k : Type*) [Field k] (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K)
    (w : ℝ) : Prop :=
  M.IsPureOfWeight ι (Nat.card k) w

/-- `M` has weights at most `w` *over the field `k`*: the bound relative to `q = #k`. See
`FrobeniusModule.IsPureOfWeightOver` for the two cardinality conventions. -/
def HasWeightsAtMostOver (k : Type*) [Field k] (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K)
    (w : ℝ) : Prop :=
  M.HasWeightsAtMost ι (Nat.card k) w

/-- A module pure of weight `w` over `k` has weights at most `w` over `k`. -/
theorem IsPureOfWeightOver.hasWeightsAtMostOver {k : Type*} [Field k] {ι : K →+* ℂ}
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeightOver k ι w) :
    M.HasWeightsAtMostOver k ι w :=
  IsPureOfWeight.hasWeightsAtMost h

/-- The Frobenius module with the same underlying space as `M` and the Frobenius of `M`
rescaled by a scalar `c`, with junk value `M` itself when `c = 0`. -/
noncomputable def rescale (M : FrobeniusModule.{u, v} K) (c : K) : FrobeniusModule.{u, v} K :=
  letI : Decidable (c = 0) := Classical.dec _
  { carrier := M.carrier
    frobenius := M.frobenius ≪≫ₗ LinearEquiv.smulOfNeZero K M.carrier (if c = 0 then 1 else c)
      (by split <;> simp_all) }

/-- The Tate twist `M(n)` relative to `q`: the same space with the geometric Frobenius
rescaled by `q ^ (-n)`. The twist `(-1)` multiplies the Frobenius by `q`, and hence raises
weights by two (`FrobeniusModule.IsPureOfWeight.tateTwist`). -/
noncomputable def tateTwist (M : FrobeniusModule.{u, v} K) (q : ℕ) (n : ℤ) :
    FrobeniusModule.{u, v} K :=
  M.rescale ((q : K) ^ (-n))

/-- The Frobenius of `M.rescale c`, for `c ≠ 0`, is `c` times the Frobenius of `M`. -/
theorem frobeniusEnd_rescale_apply {M : FrobeniusModule.{u, v} K} {c : K} (hc : c ≠ 0)
    (x : M.carrier) : (M.rescale c).frobeniusEnd x = c • M.frobeniusEnd x := by
  classical
  change (LinearEquiv.smulOfNeZero K M.carrier (if c = 0 then 1 else c) _) (M.frobenius x) = _
  simp [frobeniusEnd, if_neg hc]

/-- The eigenvalues of a rescaled Frobenius are those of the Frobenius, scaled. -/
theorem hasEigenvalue_frobeniusEnd_rescale_iff {M : FrobeniusModule.{u, v} K} {c : K}
    (hc : c ≠ 0) (α : K) :
    (M.rescale c).frobeniusEnd.HasEigenvalue (c * α) ↔ M.frobeniusEnd.HasEigenvalue α := by
  have key : ∀ x : M.carrier, (M.rescale c).frobeniusEnd x = (c * α) • x ↔
      M.frobeniusEnd x = α • x := by
    intro x
    rw [frobeniusEnd_rescale_apply hc, mul_smul]
    exact ⟨fun h ↦ smul_right_injective _ hc h, fun h ↦ by rw [h]⟩
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ((key x).1 hx.1), hx.2⟩)
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ((key x).2 hx.1), hx.2⟩)

/-- The Tate twist by `n` lowers the weight by `2 n`: the twist `(-1)` raises it by two. -/
theorem IsPureOfWeight.tateTwist {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.IsPureOfWeight ι q w) (n : ℤ) :
    (M.tateTwist q n).IsPureOfWeight ι q (w - 2 * n) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqK : (q : K) ≠ 0 := by
    intro hK
    have hnorm : ‖ι (q : K)‖ = 0 := by rw [hK, map_zero, norm_zero]
    rw [map_natCast] at hnorm
    simp only [norm_natCast] at hnorm
    exact hq0.ne' (by exact_mod_cast hnorm)
  have hc : ((q : K) ^ (-n)) ≠ 0 := zpow_ne_zero _ hqK
  intro β hβ
  obtain ⟨α, rfl⟩ : ∃ α, β = (q : K) ^ (-n) * α := ⟨((q : K) ^ (-n))⁻¹ * β, by field_simp⟩
  have hα := h α ((hasEigenvalue_frobeniusEnd_rescale_iff hc α).1 hβ)
  have hcnorm : ‖ι ((q : K) ^ (-n))‖ = (q : ℝ) ^ (-n) := by
    rw [map_zpow₀, map_natCast]
    simp
  rw [map_mul, norm_mul, hα, hcnorm, ← Real.rpow_intCast (q : ℝ) (-n), ← Real.rpow_add hq0]
  congr 1
  push_cast
  ring

/-- The *trivial* Frobenius module `K`, with the identity as Frobenius. -/
def trivial (K : Type v) [Field K] : FrobeniusModule.{v, v} K where
  carrier := K
  frobenius := LinearEquiv.refl K K

/-- An isomorphism of Frobenius modules conjugates the two Frobenius endomorphisms. -/
theorem Equiv.frobeniusEnd_eq {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    N.frobeniusEnd = e.toLinearEquiv.conj M.frobeniusEnd := by
  ext x
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
  simp [LinearEquiv.conj_apply, frobeniusEnd, e.map_frobenius]

/-- Isomorphic Frobenius modules have the same local polynomial. -/
theorem Equiv.localPolynomial_eq {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    M.localPolynomial = N.localPolynomial := by
  rw [localPolynomial, localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def,
    e.frobeniusEnd_eq, LinearEquiv.charpoly_conj]

/-- Isomorphic Frobenius modules have the same dimension. -/
theorem Equiv.finrank_eq {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    Module.finrank K M.carrier = Module.finrank K N.carrier :=
  e.toLinearEquiv.finrank_eq

/-- The local polynomial of the Tate twist `K(-d)` of the trivial Frobenius module is
`1 - qᵈ T`: its Frobenius is multiplication by `qᵈ`. -/
theorem localPolynomial_tateTwist_trivial {q : ℕ} (hq : (q : K) ≠ 0) (d : ℕ) :
    ((trivial K).tateTwist q (-d)).localPolynomial =
      1 - Polynomial.C ((q : K) ^ d) * Polynomial.X := by
  have hc : ((q : K) ^ (-(-(d : ℤ)))) ≠ 0 := zpow_ne_zero _ hq
  have hF : ((trivial K).tateTwist q (-d)).frobeniusEnd =
      ((q : K) ^ d • LinearMap.id : Module.End K K) := by
    refine LinearMap.ext fun x ↦ ?_
    refine (frobeniusEnd_rescale_apply (M := trivial K) hc x).trans ?_
    simp [frobeniusEnd, trivial]
    rfl
  rw [localPolynomial, hF]
  change LinearMap.charpolyRev ((q : K) ^ d • LinearMap.id : Module.End K K) = _
  rw [← LinearMap.charpolyRev_toMatrix (Module.Basis.singleton Unit K),
    Matrix.charpolyRev, Matrix.det_unique]
  simp [Module.Basis.toMatrix_apply, Module.Basis.singleton_repr, mul_comm]

/-- **Endpoint factors.** A Frobenius module isomorphic to the Tate twist `K(-d)` of the trivial
Frobenius module is one-dimensional with local polynomial `1 - qᵈ T`.

Applied with `d = 0` to `H⁰(X, ℚ_ℓ) ≅ ℚ_ℓ` and with `d = dim X` to `H^{2d}(X, ℚ_ℓ) ≅ ℚ_ℓ(-d)`
for a smooth proper geometrically connected `X` over `𝔽_q`, this gives the endpoint factors
`P 0 = 1 - T` and `P (2 * d) = 1 - qᵈ T` and the endpoint Betti numbers `b 0 = b (2 * d) = 1`.
The cohomological isomorphisms themselves are not available in this repository; the endpoint
factors appear in the zeta function as the fields `AlgebraicGeometry.IsWeilFactorization.apply_zero`
and `AlgebraicGeometry.IsWeilFactorization.apply_last`.
(blueprint: `prop-endpoints`) -/
theorem localPolynomial_eq_and_finrank_eq_of_equiv_tateTwist {q : ℕ} (hq : (q : K) ≠ 0)
    {d : ℕ} {M : FrobeniusModule.{v, v} K} (e : M.Equiv ((trivial K).tateTwist q (-d))) :
    M.localPolynomial = 1 - Polynomial.C ((q : K) ^ d) * Polynomial.X ∧
      Module.finrank K M.carrier = 1 :=
  ⟨e.localPolynomial_eq.trans (localPolynomial_tateTwist_trivial hq d),
    e.finrank_eq.trans (Module.finrank_self K)⟩

/-- The dual `M^∨ = Hom_K(M, K)` of a Frobenius module, with the inverse transpose
`f ↦ f ∘ F⁻¹` of the Frobenius `F`, so that the evaluation pairing `M^∨ ⊗ M → K` is
Frobenius-invariant (`FrobeniusModule.dual_frobenius_comp_frobenius`).

The carrier `Module.Dual K M.carrier` lives in universe `max u v`, since the linear maps
`M → K` involve both the carrier of `M` and the field `K`. -/
noncomputable def dual (M : FrobeniusModule.{u, v} K) : FrobeniusModule.{max u v, v} K where
  carrier := Module.Dual K M.carrier
  frobenius := M.frobenius.symm.dualMap

/-- The Frobenius of the dual `M^∨` sends a linear form `f` to `f ∘ F⁻¹`. -/
@[simp]
lemma dual_frobenius_apply (M : FrobeniusModule.{u, v} K) (f : Module.Dual K M.carrier) :
    (M.dual.frobenius f : Module.Dual K M.carrier) = f ∘ₗ M.frobenius.symm.toLinearMap :=
  rfl

/-- The evaluation pairing `M^∨ ⊗ M → K` is invariant under the Frobenius:
`(F^∨ f) (F x) = f x`. -/
lemma dual_frobenius_comp_frobenius (M : FrobeniusModule.{u, v} K)
    (f : Module.Dual K M.carrier) :
    (M.dual.frobenius f : Module.Dual K M.carrier) ∘ₗ M.frobenius.toLinearMap = f := by
  ext
  simp

end FrobeniusModule
