/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
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
- `FrobeniusModule.roots_charpoly_frobeniusEnd_eq_add`: the spectrum of the middle term of a
  short exact sequence is the union of the spectra of the outer terms.
- `FrobeniusModule.HasWeightsAtMost.of_injective`, `FrobeniusModule.HasWeightsAtMost.of_surjective`:
  submodules and quotients have weights at most those of the ambient module.
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

section Subquotient

variable {M M' M'' : FrobeniusModule.{u, v} K}

/-- A Frobenius-equivariant injection carries eigenvalues of the source to eigenvalues of the
target. -/
theorem hasEigenvalue_of_injective (f : M'.carrier →ₗ[K] M.carrier) (hf : Function.Injective f)
    (hfF : ∀ x, f (M'.frobenius x) = M.frobenius (f x)) {α : K}
    (hα : M'.frobeniusEnd.HasEigenvalue α) : M.frobeniusEnd.HasEigenvalue α := by
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := f x) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, (map_ne_zero_iff _ hf).2 hx.2⟩
  change M.frobenius (f x) = α • f x
  rw [← hfF, ← map_smul]
  exact congrArg f hx.1

/-- The Frobenius of `M` preserves the kernel of a Frobenius-equivariant map `g : M → M''`. -/
theorem ker_le_comap_frobeniusEnd (g : M.carrier →ₗ[K] M''.carrier)
    (hgF : ∀ x, g (M.frobenius x) = M''.frobenius (g x)) :
    LinearMap.ker g ≤ (LinearMap.ker g).comap M.frobeniusEnd := fun x hx ↦ by
  simp only [LinearMap.mem_ker, Submodule.mem_comap] at hx ⊢
  change g (M.frobenius x) = 0
  rw [hgF, hx, map_zero]

/-- For a Frobenius-equivariant surjection `g : M → M''`, the Frobenius induced on `M ⧸ ker g`
has the characteristic polynomial of the Frobenius of `M''`. -/
theorem charpoly_mapQ_frobeniusEnd (g : M.carrier →ₗ[K] M''.carrier)
    (hg : Function.Surjective g) (hgF : ∀ x, g (M.frobenius x) = M''.frobenius (g x)) :
    ((LinearMap.ker g).mapQ (LinearMap.ker g) M.frobeniusEnd
      (ker_le_comap_frobeniusEnd g hgF)).charpoly = M''.frobeniusEnd.charpoly := by
  let e := g.quotKerEquivOfSurjective hg
  rw [← LinearEquiv.charpoly_conj e]
  congr 1
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hg y
  rw [LinearEquiv.conj_apply_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.mapQ_apply, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact hgF x

/-- For a Frobenius-equivariant surjection `g : M → M''`, the characteristic polynomial of the
Frobenius of `M''` divides that of the Frobenius of `M`. -/
theorem charpoly_frobeniusEnd_dvd_of_surjective (g : M.carrier →ₗ[K] M''.carrier)
    (hg : Function.Surjective g) (hgF : ∀ x, g (M.frobenius x) = M''.frobenius (g x)) :
    M''.frobeniusEnd.charpoly ∣ M.frobeniusEnd.charpoly := by
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ _ _
    (ker_le_comap_frobeniusEnd g hgF), charpoly_mapQ_frobeniusEnd g hg hgF]
  exact dvd_mul_left _ _

/-- For a short exact sequence `0 → M' → M → M'' → 0` of Frobenius modules with
Frobenius-equivariant maps, the characteristic polynomial of the Frobenius of `M` is the product
of those of `M'` and `M''`. -/
theorem charpoly_frobeniusEnd_eq_mul (f : M'.carrier →ₗ[K] M.carrier)
    (g : M.carrier →ₗ[K] M''.carrier) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (hfF : ∀ x, f (M'.frobenius x) = M.frobenius (f x))
    (hgF : ∀ x, g (M.frobenius x) = M''.frobenius (g x)) :
    M.frobeniusEnd.charpoly = M'.frobeniusEnd.charpoly * M''.frobeniusEnd.charpoly := by
  have hW := ker_le_comap_frobeniusEnd g hgF
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ _ _ hW,
    charpoly_mapQ_frobeniusEnd g hg hgF]
  congr 1
  -- `f` identifies `M'` with `ker g`, intertwining the Frobenius of `M'` with its restriction
  let e : M'.carrier ≃ₗ[K] LinearMap.ker g :=
    LinearEquiv.ofInjective f hf ≪≫ₗ LinearEquiv.ofEq _ _ hfg.linearMap_ker_eq.symm
  rw [← LinearEquiv.charpoly_conj e]
  congr 1
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  obtain ⟨y, hy⟩ : (x : M.carrier) ∈ LinearMap.range f := by
    rw [← hfg.linearMap_ker_eq]
    exact x.2
  have hx : x = e y := Subtype.ext hy.symm
  subst hx
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact (hfF y).symm

/-- *Spectrum of an exact Frobenius sequence.* For a short exact sequence
`0 → M' → M → M'' → 0` of Frobenius modules with Frobenius-equivariant maps, the spectrum of the
Frobenius of `M`, the multiset of eigenvalues counted with algebraic multiplicity, is the union of
the spectra of `M'` and `M''`.

The blueprint takes the spectrum to be the multiset of `ι`-images in `ℂ` of the eigenvalues; here
it is the multiset of roots in `K` of the characteristic polynomial, which is the full spectrum
when `K` is algebraically closed, as for the coefficient field `PadicAlgCl l`.
(blueprint: `lem-a1-spectrum-exact-sequence`) -/
theorem roots_charpoly_frobeniusEnd_eq_add (f : M'.carrier →ₗ[K] M.carrier)
    (g : M.carrier →ₗ[K] M''.carrier) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (hfF : ∀ x, f (M'.frobenius x) = M.frobenius (f x))
    (hgF : ∀ x, g (M.frobenius x) = M''.frobenius (g x)) :
    M.frobeniusEnd.charpoly.roots =
      M'.frobeniusEnd.charpoly.roots + M''.frobeniusEnd.charpoly.roots := by
  rw [charpoly_frobeniusEnd_eq_mul f g hf hg hfg hfF hgF]
  exact Polynomial.roots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
    (LinearMap.charpoly_monic _).ne_zero)

/-- *Subquotient bounds, submodule case.* A Frobenius module embedding Frobenius-equivariantly
into one with weights at most `w` has weights at most `w`.
(blueprint: `lem-a1-subquotient-extension-bounds`) -/
theorem HasWeightsAtMost.of_injective {ι : K →+* ℂ} {q : ℕ} {w : ℝ}
    (f : M'.carrier →ₗ[K] M.carrier) (hf : Function.Injective f)
    (hfF : ∀ x, f (M'.frobenius x) = M.frobenius (f x)) (h : M.HasWeightsAtMost ι q w) :
    M'.HasWeightsAtMost ι q w :=
  fun α hα ↦ h α (hasEigenvalue_of_injective f hf hfF hα)

/-- *Subquotient bounds, quotient case.* A Frobenius-equivariant quotient of a Frobenius module
with weights at most `w` has weights at most `w`: the characteristic polynomial of the quotient
divides that of the ambient module (`lem-a1-spectrum-exact-sequence`), so every eigenvalue of the
quotient is an eigenvalue of the ambient module.
(blueprint: `lem-a1-subquotient-extension-bounds`) -/
theorem HasWeightsAtMost.of_surjective {ι : K →+* ℂ} {q : ℕ} {w : ℝ}
    (g : M.carrier →ₗ[K] M''.carrier) (hg : Function.Surjective g)
    (hgF : ∀ x, g (M.frobenius x) = M''.frobenius (g x)) (h : M.HasWeightsAtMost ι q w) :
    M''.HasWeightsAtMost ι q w := by
  intro α hα
  refine h α ?_
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα ⊢
  obtain ⟨p, hp⟩ := charpoly_frobeniusEnd_dvd_of_surjective g hg hgF
  rw [Polynomial.IsRoot, hp, Polynomial.eval_mul, hα, zero_mul]

end Subquotient

end FrobeniusModule
