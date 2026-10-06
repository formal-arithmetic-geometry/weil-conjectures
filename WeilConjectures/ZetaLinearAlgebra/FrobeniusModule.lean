/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable

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

/-- The identity isomorphism of a Frobenius module. -/
def Equiv.refl (M : FrobeniusModule.{u, v} K) : M.Equiv M where
  toLinearEquiv := LinearEquiv.refl K M.carrier
  map_frobenius _ := rfl

/-- The inverse of an isomorphism of Frobenius modules. -/
noncomputable def Equiv.symm {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) : N.Equiv M where
  toLinearEquiv := e.toLinearEquiv.symm
  map_frobenius y := by
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, e.map_frobenius, LinearEquiv.apply_symm_apply]

/-- The composite of two isomorphisms of Frobenius modules. -/
def Equiv.trans {M N P : FrobeniusModule.{u, v} K} (e : M.Equiv N) (e' : N.Equiv P) :
    M.Equiv P where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  map_frobenius x := by
    simp only [LinearEquiv.trans_apply, e.map_frobenius, e'.map_frobenius]

/-- Two zero Frobenius modules are isomorphic. -/
noncomputable def Equiv.ofSubsingleton (M N : FrobeniusModule.{u, v} K)
    [Subsingleton M.carrier] [Subsingleton N.carrier] : M.Equiv N where
  toLinearEquiv := LinearEquiv.ofSubsingleton _ _
  map_frobenius _ := Subsingleton.elim _ _

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

section Weights

/-- The Frobenius endomorphism agrees with the Frobenius automorphism. -/
@[simp]
lemma frobeniusEnd_apply (M : FrobeniusModule.{u, v} K) (x : M.carrier) :
    M.frobeniusEnd x = M.frobenius x :=
  rfl

/-- The Frobenius of a zero Frobenius module has no eigenvalues. -/
theorem not_hasEigenvalue_of_subsingleton (M : FrobeniusModule.{u, v} K)
    [Subsingleton M.carrier] (α : K) : ¬ M.frobeniusEnd.HasEigenvalue α := by
  intro h
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  exact hx.2 (Subsingleton.elim x 0)

/-- A zero Frobenius module is pure of every weight. -/
theorem isPureOfWeight_of_subsingleton (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K)
    [Subsingleton M.carrier] (w : ℝ) : M.IsPureOfWeight ι q w :=
  fun α hα ↦ absurd hα (M.not_hasEigenvalue_of_subsingleton α)

/-- A zero Frobenius module has weights at most every `w`. -/
theorem hasWeightsAtMost_of_subsingleton (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K)
    [Subsingleton M.carrier] (w : ℝ) : M.HasWeightsAtMost ι q w :=
  (isPureOfWeight_of_subsingleton ι q M w).hasWeightsAtMost

/-- A zero Frobenius module is pure of every weight over `k`. -/
theorem isPureOfWeightOver_of_subsingleton (k : Type*) [Field k] (ι : K →+* ℂ)
    (M : FrobeniusModule.{u, v} K) [Subsingleton M.carrier] (w : ℝ) :
    M.IsPureOfWeightOver k ι w :=
  isPureOfWeight_of_subsingleton ι _ M w

/-- A zero Frobenius module has weights at most every `w` over `k`. -/
theorem hasWeightsAtMostOver_of_subsingleton (k : Type*) [Field k] (ι : K →+* ℂ)
    (M : FrobeniusModule.{u, v} K) [Subsingleton M.carrier] (w : ℝ) :
    M.HasWeightsAtMostOver k ι w :=
  hasWeightsAtMost_of_subsingleton ι _ M w

/-- A Frobenius module isomorphic to one pure of weight `w` is pure of weight `w`. -/
theorem IsPureOfWeight.of_equiv {ι : K →+* ℂ} {q : ℕ} {M N : FrobeniusModule.{u, v} K}
    (e : M.Equiv N) {w : ℝ} (h : N.IsPureOfWeight ι q w) : M.IsPureOfWeight ι q w :=
  fun α hα ↦ h α (e.hasEigenvalue hα)

/-- A Frobenius module isomorphic to one pure of weight `w` over `k` is pure of weight `w`
over `k`. -/
theorem IsPureOfWeightOver.of_equiv {k : Type*} [Field k] {ι : K →+* ℂ}
    {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) {w : ℝ} (h : N.IsPureOfWeightOver k ι w) :
    M.IsPureOfWeightOver k ι w :=
  IsPureOfWeight.of_equiv e h

/-- A Frobenius module isomorphic to one with weights at most `w` over `k` has weights at most
`w` over `k`. -/
theorem HasWeightsAtMostOver.of_equiv {k : Type*} [Field k] {ι : K →+* ℂ}
    {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) {w : ℝ}
    (h : N.HasWeightsAtMostOver k ι w) : M.HasWeightsAtMostOver k ι w :=
  HasWeightsAtMost.of_equiv e h

/-- Weights at most `w` are stable under extensions (blueprint: `lem-a1-extension-bounds`):
given Frobenius-equivariant maps `f : M₁ → M₂` and `g : M₂ → M₃` with `f` injective and
`ker g = range f`, if `M₁` and `M₃` have weights at most `w`, then so does `M₂`. Every
eigenvalue of `M₂` is an eigenvalue of `M₁` or of `M₃`. Surjectivity of `g` is not needed. -/
theorem HasWeightsAtMost.of_injective_of_exact {ι : K →+* ℂ} {q : ℕ}
    {M₁ M₂ M₃ : FrobeniusModule.{u, v} K} (f : M₁.carrier →ₗ[K] M₂.carrier)
    (g : M₂.carrier →ₗ[K] M₃.carrier) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hf' : ∀ x, f (M₁.frobenius x) = M₂.frobenius (f x))
    (hg' : ∀ x, g (M₂.frobenius x) = M₃.frobenius (g x)) {w : ℝ}
    (h₁ : M₁.HasWeightsAtMost ι q w) (h₃ : M₃.HasWeightsAtMost ι q w) :
    M₂.HasWeightsAtMost ι q w := by
  intro α hα
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, frobeniusEnd_apply] at hv
  by_cases hgv : g v = 0
  · obtain ⟨u, rfl⟩ := (hfg v).1 hgv
    refine h₁ α (Module.End.hasEigenvalue_of_hasEigenvector (x := u) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, frobeniusEnd_apply]
    refine ⟨hf ?_, fun hu ↦ hv.2 (by simp [hu])⟩
    rw [map_smul, hf', hv.1]
  · refine h₃ α (Module.End.hasEigenvalue_of_hasEigenvector (x := g v) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, frobeniusEnd_apply,
      ← hg', hv.1, map_smul]
    exact ⟨rfl, hgv⟩

/-- The version of `FrobeniusModule.HasWeightsAtMost.of_injective_of_exact` over a field `k`
(blueprint: `lem-a1-extension-bounds`). -/
theorem HasWeightsAtMostOver.of_injective_of_exact {k : Type*} [Field k] {ι : K →+* ℂ}
    {M₁ M₂ M₃ : FrobeniusModule.{u, v} K} (f : M₁.carrier →ₗ[K] M₂.carrier)
    (g : M₂.carrier →ₗ[K] M₃.carrier) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hf' : ∀ x, f (M₁.frobenius x) = M₂.frobenius (f x))
    (hg' : ∀ x, g (M₂.frobenius x) = M₃.frobenius (g x)) {w : ℝ}
    (h₁ : M₁.HasWeightsAtMostOver k ι w) (h₃ : M₃.HasWeightsAtMostOver k ι w) :
    M₂.HasWeightsAtMostOver k ι w :=
  HasWeightsAtMost.of_injective_of_exact f g hf hfg hf' hg' h₁ h₃

/-- Weight bounds can be checked on a power of the Frobenius (blueprint:
`lem-a1-weight-bound-constant-extension`): if every eigenvalue `μ` of `F ^ m`, `m > 0`,
satisfies `|ι μ| ≤ (q ^ m) ^ (b / 2)`, then `M` has weights at most `b` relative to `q`. This
is the passage from the constant field extension of degree `m`, where the Frobenius is `F ^ m`
and the cardinality is `q ^ m`, back to the base. -/
theorem hasWeightsAtMost_of_pow {ι : K →+* ℂ} {q : ℕ} (M : FrobeniusModule.{u, v} K) {m : ℕ}
    (hm : 0 < m) {b : ℝ}
    (h : ∀ μ, (M.frobeniusEnd ^ m).HasEigenvalue μ → ‖ι μ‖ ≤ ((q : ℝ) ^ m) ^ (b / 2)) :
    M.HasWeightsAtMost ι q b := by
  intro α hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  have hpow := h (α ^ m) (Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    (Module.End.hasEigenvector_iff.2
      ⟨Module.End.mem_eigenspace_iff.2 (hx.pow_apply m), hx.2⟩))
  rw [map_pow, norm_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q), mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg q)] at hpow
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hm.ne').1 hpow

/-- Let `p ≤ p'` be subspaces stable under an endomorphism `f`, with `p'` of dimension one more
than `p`. Then `f` acts on the one-dimensional quotient `p' / p` by a scalar `μ`, that is
`f x - μ • x ∈ p` for all `x ∈ p'`, and `μ` is an eigenvalue of `f`, since `f - μ` maps `p'`
into the smaller space `p` and so is not injective on `p'`. -/
theorem _root_.Module.End.exists_hasEigenvalue_forall_sub_smul_mem {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    {p p' : Submodule K V} (hle : p ≤ p')
    (hdim : Module.finrank K p' = Module.finrank K p + 1) (hp : ∀ x ∈ p, f x ∈ p)
    (hp' : ∀ x ∈ p', f x ∈ p') :
    ∃ μ : K, f.HasEigenvalue μ ∧ ∀ x ∈ p', f x - μ • x ∈ p := by
  have hlt : p < p' := lt_of_le_of_ne hle fun h ↦ by
    subst h
    omega
  obtain ⟨x, hxp', hxp⟩ := SetLike.exists_of_lt hlt
  have hsup : p ⊔ K ∙ x = p' := by
    refine Submodule.eq_of_le_of_finrank_le
      (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hxp')) ?_
    have := Submodule.finrank_lt_finrank_of_lt
      (left_lt_sup.2 fun h ↦ hxp ((Submodule.span_singleton_le_iff_mem _ _).1 h))
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hsup ▸ hp' x hxp')
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hsub : ∀ v ∈ p', f v - μ • v ∈ p := by
    intro v hv
    obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.1 (hsup ▸ hv)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz'
    have hfx : f x - μ • x = y := by
      rw [← hyz]
      abel
    have : f (y' + c • x) - μ • (y' + c • x) = (f y' - μ • y') + c • (f x - μ • x) := by
      rw [map_add, map_smul, smul_add, smul_comm μ c x, smul_sub]
      abel
    rw [this, hfx]
    exact p.add_mem (p.sub_mem (hp y' hy') (p.smul_mem μ hy')) (p.smul_mem c hy)
  refine ⟨μ, ?_, hsub⟩
  let g : p' →ₗ[K] p := (f - μ • 1).restrict (p := p') (q := p) fun v hv ↦ by
    simpa using hsub v hv
  have hker : LinearMap.ker g ≠ ⊥ := fun hker ↦ by
    have := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.1 hker)
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hker
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := (v : V)) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, by simpa using hv0⟩
  rw [LinearMap.mem_ker, Subtype.ext_iff] at hv
  simpa [g, sub_eq_zero] using hv

/-- A Frobenius module with weights at most `w` over an algebraically closed field is mixed of
weights at most `w` in the filtration sense (blueprint: `lem-a1-punctual-bound-module-mixed`).
`FrobeniusModule.HasWeightsAtMost` is the eigenvalue form of "mixed of weights at most `w`":
every eigenvalue `α` of the Frobenius `F` satisfies `|ι α| ≤ q ^ (w / 2)`. This lemma produces
the filtration form: a complete `F`-stable flag `0 = V 0 ⊂ ⋯ ⊂ V n = M`, with `dim V i = i`, on
each of whose one-dimensional graded pieces `V (i + 1) / V i` the Frobenius acts by a scalar
`μ` with `|ι μ| ≤ q ^ (w / 2)`, so that each graded piece is pure of weight at most `w`. -/
theorem HasWeightsAtMost.exists_flag [IsAlgClosed K] {ι : K →+* ℂ} {q : ℕ}
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.HasWeightsAtMost ι q w) :
    ∃ V : Fin (Module.finrank K M.carrier + 1) → Submodule K M.carrier,
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last _) = ⊤ ∧ (∀ i, Module.finrank K (V i) = i) ∧
      ∀ i : Fin (Module.finrank K M.carrier), ∃ μ : K, ‖ι μ‖ ≤ (q : ℝ) ^ (w / 2) ∧
        ∀ x ∈ V i.succ, M.frobeniusEnd x - μ • x ∈ V i.castSucc := by
  obtain ⟨V, hmono, hinv, hdim⟩ := M.frobeniusEnd.exists_complete_invariant_flag
  refine ⟨V, hmono, ?_, ?_, hdim, fun i ↦ ?_⟩
  · rw [← Submodule.finrank_eq_zero, hdim, Fin.val_zero]
  · exact Submodule.eq_top_of_finrank_eq (by rw [hdim, Fin.val_last])
  · obtain ⟨μ, hμ, hsub⟩ := M.frobeniusEnd.exists_hasEigenvalue_forall_sub_smul_mem
      (hmono (Fin.castSucc_le_succ i)) (by rw [hdim, hdim, Fin.val_succ, Fin.val_castSucc])
      (fun x hx ↦ hinv _ (Submodule.mem_map_of_mem hx))
      (fun x hx ↦ hinv _ (Submodule.mem_map_of_mem hx))
    exact ⟨μ, h μ hμ, hsub⟩

end Weights

end FrobeniusModule
