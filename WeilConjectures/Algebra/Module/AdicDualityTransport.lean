/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicPairingLimit
public import WeilConjectures.Algebra.Module.RationalPerfectPairing

/-!
# Transport of finite-level duality to an extension of `ℚ_p`

This file proves the linear algebra of the transport of Poincaré duality from the finite
coefficient rings `ℤ/ℓᵐ` to `ℚ̄_ℓ` (blueprint `sk-thm-transport`,
`thm-pod-qbar-coefficient-pairing`), in the following abstract form
(`LinearMap.exists_isPerfPair_of_finiteLevel`).

Let `A`, `B` be finitely generated `ℤ_p`-modules (the integral cohomology groups `Hⁱ(X, ℤ_ℓ)`,
`H^{2d-i}(X, ℤ_ℓ)`) with endomorphisms `F_A`, `F_B` (Frobenius), and let `V`, `W` be their
extensions of scalars to a field `K ⊇ ℤ_p` (e.g. `ℚ̄_ℓ`), with the induced endomorphisms. Suppose
that for every `m`:

* there are maps `ρ : A ⟶ Eₘ`, `σ : B ⟶ Fₘ` to modules (the cohomology groups with coefficients
  `ℤ/ℓᵐ`) whose kernels are `pᵐ A`, `pᵐ B` and whose images contain `pᵉ Eₘ`, `pᵉ Fₘ` for a fixed
  `e` (the Bockstein sequences, when `pᵉ` kills the torsion of the cohomology);
* there is a pairing `Qₘ : Eₘ × Fₘ ⟶ ℤ_p / pᵐ`, nondegenerate on both sides (finite-level
  Poincaré duality), whose restriction along `ρ`, `σ` is a `c`-similitude for `F_A`, `F_B`.

The finite-level pairings need not be compatible with each other. Then there is a perfect
`K`-bilinear pairing `V × W ⟶ K` which is a `c`-similitude for the induced endomorphisms. It is
obtained by compactness (`LinearMap.exists_isSimilitude_of_forall_level`) on the free quotients
of `A` and `B`, followed by extension of scalars (`LinearMap.isPerfPair_of_span_eq_top`).
-/

@[expose] public section

open Function

namespace LinearMap

variable {p : ℕ} [Fact p.Prime]

section Torsion

variable {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]

/-- Over `ℤ_p`, a torsion element is killed by a power of `p`. -/
lemma exists_pow_smul_eq_zero_of_mem_torsion {a : A} (ha : a ∈ Submodule.torsion ℤ_[p] A) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • a = 0 := by
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  refine ⟨r.valuation, ?_⟩
  have hr' : r • a = 0 := hra
  set u := PadicInt.unitCoeff hr0
  have hu : r = ↑u * (p : ℤ_[p]) ^ r.valuation := PadicInt.unitCoeff_spec hr0
  have h1 : ((↑u⁻¹ : ℤ_[p]) * r) • a = 0 := by
    rw [mul_smul, hr', smul_zero]
  rwa [hu, ← mul_assoc, Units.inv_mul, one_mul] at h1

/-- In a finitely generated `ℤ_p`-module, a single power of `p` kills the torsion. -/
lemma exists_pow_smul_eq_zero_of_finite [Module.Finite ℤ_[p] A] :
    ∃ c : ℕ, ∀ a ∈ Submodule.torsion ℤ_[p] A, (p : ℤ_[p]) ^ c • a = 0 := by
  obtain ⟨c, hc⟩ := Submodule.exists_pow_smul_eq_zero_of_isNoetherian (A := A) (p : ℤ_[p])
  exact ⟨c, fun a ha ↦ hc a (exists_pow_smul_eq_zero_of_mem_torsion ha)⟩

end Torsion

section Descent

variable {A B M : Type*} [AddCommGroup A] [Module ℤ_[p] A] [AddCommGroup B] [Module ℤ_[p] B]
  [AddCommGroup M] [Module ℤ_[p] M]

/-- A bilinear map killing torsion in both variables is determined by its values on lifts of
bases of the free quotients by torsion. -/
lemma eq_of_eq_on_lifts [Module.Finite ℤ_[p] A] [Module.Finite ℤ_[p] B]
    {I J : Type*} [Finite I] [Finite J]
    (bA : Module.Basis I ℤ_[p] (A ⧸ Submodule.torsion ℤ_[p] A))
    (bB : Module.Basis J ℤ_[p] (B ⧸ Submodule.torsion ℤ_[p] B)) (aI : I → A) (bJ : J → B)
    (haI : ∀ i, (Submodule.torsion ℤ_[p] A).mkQ (aI i) = bA i)
    (hbJ : ∀ j, (Submodule.torsion ℤ_[p] B).mkQ (bJ j) = bB j)
    (P P' : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] M)
    (hA : ∀ t ∈ Submodule.torsion ℤ_[p] A, P t = P' t)
    (hB : ∀ t ∈ Submodule.torsion ℤ_[p] B, P.flip t = P'.flip t)
    (h : ∀ i j, P (aI i) (bJ j) = P' (aI i) (bJ j)) : P = P' := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have hdecA (x : A) : x - ∑ i, bA.repr ((Submodule.torsion ℤ_[p] A).mkQ x) i • aI i ∈
      Submodule.torsion ℤ_[p] A := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, haI, Module.Basis.sum_repr, sub_self]
  have hdecB (y : B) : y - ∑ j, bB.repr ((Submodule.torsion ℤ_[p] B).mkQ y) j • bJ j ∈
      Submodule.torsion ℤ_[p] B := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hbJ, Module.Basis.sum_repr, sub_self]
  ext x y
  have hx := hA _ (hdecA x)
  have hy := hB _ (hdecB y)
  rw [← sub_add_cancel x (∑ i, bA.repr ((Submodule.torsion ℤ_[p] A).mkQ x) i • aI i), map_add,
    map_add, add_apply, add_apply, hx]
  congr 1
  rw [← sub_add_cancel y (∑ j, bB.repr ((Submodule.torsion ℤ_[p] B).mkQ y) j • bJ j)]
  have hy' := congr($hy (∑ i, bA.repr ((Submodule.torsion ℤ_[p] A).mkQ x) i • aI i))
  simp only [flip_apply] at hy'
  rw [map_add, map_add, hy']
  congr 1
  simp only [map_sum, map_smul, sum_apply, smul_apply, h]

end Descent

section Transport

variable {A B : Type*} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A]
  [AddCommGroup B] [Module ℤ_[p] B] [Module.Finite ℤ_[p] B]
  (FA : A →ₗ[ℤ_[p]] A) (FB : B →ₗ[ℤ_[p]] B) (c : ℤ_[p]) (e : ℕ)
  {E F : ℕ → Type*} [∀ m, AddCommGroup (E m)] [∀ m, Module ℤ_[p] (E m)]
  [∀ m, AddCommGroup (F m)] [∀ m, Module ℤ_[p] (F m)]
  (ρ : ∀ m, A →ₗ[ℤ_[p]] E m) (σ : ∀ m, B →ₗ[ℤ_[p]] F m)
  (Q : ∀ m, E m →ₗ[ℤ_[p]] F m →ₗ[ℤ_[p]] ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})

/-- **Integral duality from finite-level dualities.** Under the finite-level hypotheses of
`LinearMap.exists_isPerfPair_of_finiteLevel`, there is a `c`-similitude `A × B ⟶ ℤ_p` with
torsion left and right kernels. -/
theorem exists_isSimilitude_torsion_of_finiteLevel
    (hkerA : ∀ m a, ρ m a = 0 → ∃ a', a = (p : ℤ_[p]) ^ m • a')
    (hkerB : ∀ m b, σ m b = 0 → ∃ b', b = (p : ℤ_[p]) ^ m • b')
    (hrangeE : ∀ m (y : E m), (p : ℤ_[p]) ^ e • y ∈ range (ρ m))
    (hrangeF : ∀ m (y : F m), (p : ℤ_[p]) ^ e • y ∈ range (σ m))
    (hQl : ∀ m, Injective (Q m)) (hQr : ∀ m, Injective (Q m).flip)
    (hQF : ∀ m a b, Q m (ρ m (FA a)) (σ m (FB b)) = c • Q m (ρ m a) (σ m b)) :
    ∃ P : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p], (∀ a b, P (FA a) (FB b) = c * P a b) ∧
      (∀ a, P a = 0 → a ∈ Submodule.torsion ℤ_[p] A) ∧
      (∀ b, P.flip b = 0 → b ∈ Submodule.torsion ℤ_[p] B) := by
  classical
  obtain ⟨cA, hcA⟩ := exists_pow_smul_eq_zero_of_finite (p := p) (A := A)
  obtain ⟨cB, hcB⟩ := exists_pow_smul_eq_zero_of_finite (p := p) (A := B)
  let TA := Submodule.torsion ℤ_[p] A
  let TB := Submodule.torsion ℤ_[p] B
  have hTA : TA ≤ TA.comap FA := fun a ha ↦ by
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_mem_torsion ha
    exact ⟨⟨(p : ℤ_[p]) ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)) n⟩, by
        change (p : ℤ_[p]) ^ n • FA a = 0
        rw [← map_smul, hn, map_zero]⟩
  have hTB : TB ≤ TB.comap FB := fun b hb ↦ by
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_mem_torsion hb
    exact ⟨⟨(p : ℤ_[p]) ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)) n⟩, by
        change (p : ℤ_[p]) ^ n • FB b = 0
        rw [← map_smul, hn, map_zero]⟩
  let FA' := TA.mapQ TA FA hTA
  let FB' := TB.mapQ TB FB hTB
  let bA := Module.Free.chooseBasis ℤ_[p] (A ⧸ TA)
  let bB := Module.Free.chooseBasis ℤ_[p] (B ⧸ TB)
  let aI (i : Module.Free.ChooseBasisIndex ℤ_[p] (A ⧸ TA)) : A :=
    (Submodule.mkQ_surjective TA (bA i)).choose
  have haI (i) : TA.mkQ (aI i) = bA i := (Submodule.mkQ_surjective TA (bA i)).choose_spec
  let bJ (j : Module.Free.ChooseBasisIndex ℤ_[p] (B ⧸ TB)) : B :=
    (Submodule.mkQ_surjective TB (bB j)).choose
  have hbJ (j) : TB.mkQ (bJ j) = bB j := (Submodule.mkQ_surjective TB (bB j)).choose_spec
  -- the finite-level pairings, made to kill torsion
  let P0 (m : ℕ) : A →ₗ[ℤ_[p]] B →ₗ[ℤ_[p]] ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m} :=
    (Q m).compl₁₂ ((ρ m) ∘ₗ ((p : ℤ_[p]) ^ cA • LinearMap.id))
      ((σ m) ∘ₗ ((p : ℤ_[p]) ^ cB • LinearMap.id))
  have hP0 (m : ℕ) (a : A) (b : B) :
      P0 m a b = Q m (ρ m ((p : ℤ_[p]) ^ cA • a)) (σ m ((p : ℤ_[p]) ^ cB • b)) := rfl
  -- integral lifts of the finite-level pairings on the free quotients
  let G (m : ℕ) : Matrix _ _ ℤ_[p] := fun i j ↦ Quotient.out (P0 m (aI i) (bJ j))
  let Pm (m : ℕ) : (A ⧸ TA) →ₗ[ℤ_[p]] (B ⧸ TB) →ₗ[ℤ_[p]] ℤ_[p] := Matrix.toLinearMap₂ bA bB (G m)
  have hPm (m : ℕ) (a : A) (b : B) :
      Ideal.Quotient.mk _ (Pm m (TA.mkQ a) (TB.mkQ b)) = P0 m a b := by
    sorry
  sorry

end Transport

end LinearMap
