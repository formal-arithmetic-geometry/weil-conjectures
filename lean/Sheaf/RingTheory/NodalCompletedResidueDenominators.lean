/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Denominators and residues in a completed series algebra

Source: Stacks Project, curves.tex, Tag 0CBT (remark-quadratic-extension), omitted
comparison of constructions (2) and (3)
(blueprint: lem-sfb-nodal-completed-residue-denominators).

The two quotient equivalences are specified on every quotient representative. Together
with `hconstant`, these formulas express their residue-field algebra compatibility,
without choosing a second algebra structure on either quotient. The condition `hscalar`
expresses that the ring equivalence `psi` is an algebra equivalence for the canonical
right-factor action of the completion.

## Main statements

* `nodal_completed_residue_denominators`: canonical residue comparisons, regular
  denominators, ideal powers, the division residue formula, and invertible ratios.
* `nodal_completed_residue_denominators_nonunit_counterexample`: a nonzero leading
  coefficient does not suffice, using the two-branch equal-constant-term ring over Q.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RingTheory

/-- Descend the canonical residue comparison and regular denominators from a series model.

Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)/(3)
(blueprint: lem-sfb-nodal-completed-residue-denominators).

Proof (the first six steps of the node):
1. The completion of the Noetherian local ring A is faithfully flat, by local-completion-
   faithfully-flat. Its base change B to C is faithfully flat, by faithfully-flat-base-
   change, hence injective by faithfully-flat-ideal-contraction. Thus A embeds in C too.
2. Local-completion-local-ring identifies R/mR with F. Tensor-over-quotient-ring gives
   C/mC = B tensor_A F = B/mB. The maps send b to b tensor 1 and b tensor r to b times
   the residue of r. They are multiplicative and inverse. Evaluation at zero on L[[t]]
   has kernel (t), with constants as a section. This gives the second quotient equivalence.
   The hypothesis on constants makes both equivalences F-algebra equivalences.
3. Write psi(f) = t U, where U = u + t h. Power-series-unit-constant-coefficient makes
   U a unit. Multiplication by t is injective by shifting coefficients, so t U is regular.
   The injective maps of step 1 give regularity on A and B, including zero-divisor L.
4. In C the ideals fC and mC are both (t). Faithfully-flat-ideal-contraction gives
   fB = mB. Extension commutes with ideal products, hence m^n B = f^n B, also for n = 0.
5. If d belongs to m^n, step 4 gives f^n b = d, and regularity gives uniqueness. If
   psi(d) = r t^n + t^(n+1) h_d, compare degree-n coefficients in t^n U^n psi(b) = psi(d).
   This gives u^n psi(b)(0) = r and hence the stated residue r times u^(-n).
6. Apply step 4 to f and g to obtain g = fb and f = gc. Then f(bc - 1) = 0;
   regularity gives bc = 1, and commutativity gives cb = 1. These are the unique ratios.
-/
theorem nodal_completed_residue_denominators
    (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    [CommRing L] [Nontrivial L] [Algebra (A ⧸ IsLocalRing.maximalIdeal A) L]
    [Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) (PowerSeries L)]
    (hinj : Function.Injective (algebraMap A B))
    (psi : (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃+* PowerSeries L)
    (hscalar : ∀ r : AdicCompletion (IsLocalRing.maximalIdeal A) A,
      psi (1 ⊗ₜ[A] r) =
        algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A) (PowerSeries L) r)
    (hideal : ((IsLocalRing.maximalIdeal A).map
      (algebraMap A (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))).map
        psi.toRingHom = Ideal.span {PowerSeries.X})
    (hconstant : ∀ a : A,
      PowerSeries.constantCoeff (psi (algebraMap A B a ⊗ₜ[A] 1)) =
        algebraMap (A ⧸ IsLocalRing.maximalIdeal A) L
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) :
    ∃ (e₁ : (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ≃+*
        ((B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸
          (IsLocalRing.maximalIdeal A).map
            (algebraMap A (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))))
      (e₂ : ((B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸
          (IsLocalRing.maximalIdeal A).map
            (algebraMap A (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A))) ≃+* L),
      (∀ b : B, e₁ (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (b ⊗ₜ[A] 1)) ∧
      (∀ z : B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A,
        e₂ (Ideal.Quotient.mk _ z) = PowerSeries.constantCoeff (psi z)) ∧
      (∀ (f : A) (u₀ : Lˣ) (h : PowerSeries L),
        f ∈ IsLocalRing.maximalIdeal A →
        psi (algebraMap A B f ⊗ₜ[A] 1) =
          PowerSeries.C (u₀ : L) * PowerSeries.X + PowerSeries.X ^ 2 * h →
        Function.Injective (fun a : A ↦ f * a) ∧
        Function.Injective (fun b : B ↦ algebraMap A B f * b) ∧
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          Ideal.span {algebraMap A B f} ∧
        (∀ n : ℕ, ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A B) =
          Ideal.span {(algebraMap A B f) ^ n}) ∧
        (∀ (n : ℕ) (d : A), d ∈ (IsLocalRing.maximalIdeal A) ^ n →
          (∃! b : B, (algebraMap A B f) ^ n * b = algebraMap A B d) ∧
          (∀ (b : B), (algebraMap A B f) ^ n * b = algebraMap A B d →
            ∀ (r : L) (h_d : PowerSeries L),
              psi (algebraMap A B d ⊗ₜ[A] 1) =
                PowerSeries.C r * PowerSeries.X ^ n + PowerSeries.X ^ (n + 1) * h_d →
              e₂ (e₁ (Ideal.Quotient.mk _ b)) = r * ((↑(u₀⁻¹) : L) ^ n))) ∧
        (∀ (g : A) (v₀ : Lˣ) (h_g : PowerSeries L),
          g ∈ IsLocalRing.maximalIdeal A →
          psi (algebraMap A B g ⊗ₜ[A] 1) =
            PowerSeries.C (v₀ : L) * PowerSeries.X + PowerSeries.X ^ 2 * h_g →
          ∃ b c : B, algebraMap A B f * b = algebraMap A B g ∧
            algebraMap A B g * c = algebraMap A B f ∧ b * c = 1 ∧ c * b = 1)) := by
  sorry

/-- A nonzero, nonunit leading coefficient can fail both regularity and ideal generation.

Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)/(3); explicit
counterexample of the node's proof, step 7
(blueprint: lem-sfb-nodal-completed-residue-denominators).

Proof (step 7): take B = Q[[x]] times Q[[y]], A the equal-constant pairs, m the pairs
with constant zero, and L = Q times Q. The map Q[[x,y]] onto A sends a series to its
axis restrictions; lift (p,q) by p(x)+q(y)-p(0). Power-series-noetherian and passage to
quotients make A Noetherian. The unit-constant-coefficient criterion shows that A is
local with residue Q. Its maximal ideal is generated by (x,0),(0,y), and its positive
powers are x^n Q[[x]] times y^n Q[[y]]. Stabilizing coefficients show A is complete.
Thus B tensor_A completed A = B. Sending (p,q) to the series with coefficients (p_i,q_i)
is the required completed-model isomorphism, carries mB to (t), and has diagonal
residues from A. Take f=(x,0), whose leading coefficient (1,0) is nonzero and not a
unit. It kills (0,y) in A, so is not regular; fB=xQ[[x]] times 0 is strictly smaller
than mB. These formulas are valid also in characteristic two over another field.
-/
theorem nodal_completed_residue_denominators_nonunit_counterexample :
    ∃ (S : Subring (PowerSeries ℚ × PowerSeries ℚ)) (m : Ideal S),
      (∀ a : PowerSeries ℚ × PowerSeries ℚ,
        a ∈ S ↔ PowerSeries.constantCoeff a.1 = PowerSeries.constantCoeff a.2) ∧
      IsNoetherianRing S ∧ IsLocalRing S ∧ IsAdicComplete m S ∧ m.IsMaximal ∧
      (∀ I : Ideal S, I.IsMaximal → I = m) ∧
      (∃ rho : (S ⧸ m) ≃+* ℚ, ∀ a : S,
        rho (Ideal.Quotient.mk m a) = PowerSeries.constantCoeff a.val.1) ∧
      (∃ psi : ((PowerSeries ℚ × PowerSeries ℚ) ⊗[S] AdicCompletion m S) ≃+*
          PowerSeries (ℚ × ℚ),
        (∀ (b : PowerSeries ℚ × PowerSeries ℚ) (n : ℕ),
          PowerSeries.coeff n (psi (b ⊗ₜ[S] 1)) =
            (PowerSeries.coeff n b.1, PowerSeries.coeff n b.2)) ∧
        (m.map (algebraMap S
          ((PowerSeries ℚ × PowerSeries ℚ) ⊗[S] AdicCompletion m S))).map
            psi.toRingHom = Ideal.span {PowerSeries.X} ∧
        ∃ (f : S) (h : PowerSeries (ℚ × ℚ)), f ∈ m ∧
          psi (f.val ⊗ₜ[S] 1) =
            PowerSeries.C (1, 0) * PowerSeries.X + PowerSeries.X ^ 2 * h ∧
          ((1, 0) : ℚ × ℚ) ≠ 0 ∧ ¬ IsUnit ((1, 0) : ℚ × ℚ) ∧
          ¬ Function.Injective (fun a : S ↦ f * a) ∧
          m.map (algebraMap S (PowerSeries ℚ × PowerSeries ℚ)) ≠
            Ideal.span {f.val}) := by
  sorry

end RingTheory
