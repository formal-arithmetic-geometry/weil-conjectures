/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.ContinuousMap.Algebra
import Sheaf.Analysis.FiniteQuotientContractiveAverage
import Sheaf.Topology.OpenNormalQuotientFunctionsDense
import Sheaf.Topology.CompactParameterFunctional

/-!
# Complete-scalar averaging on pro-prime-to-ell groups

Source: blueprint main-20261015, six-functors basics, direct-image stability proof,
paragraph (3), scalar tame-kernel analytic input. The blueprint supplies the geometric
context; the analytic assertion and argument are agent-formulated, with an exact
literature reference WANTED (blueprint: lem-sfb-prime-to-ell-complete-scalar-integral).
-/

@[expose] public section

universe u v w

namespace WeilConjectures

/-- A contractive normalized two-sided invariant integral, including continuous profinite
parameters, their continuous-function scalar action, precomposition, and finite sums.
Source: blueprint main-20261015, direct-image stability proof, paragraph (3), scalar
analytic input (blueprint: lem-sfb-prime-to-ell-complete-scalar-integral).

Proof plan (agent analytic expansion; exact literature reference WANTED):
1. Compactness makes every open-normal quotient finite. Functions factoring through such
quotients form a B-linear subspace D containing the constants, by common refinement.
2. For V contained in U, every fibre of K/V to K/U has cardinality |U/V|. Partitioning the
finite sum by these fibres proves compatibility of normalized averages. Refining two
quotients by their intersection makes the average A on D well defined and B-linear.
3. The prime-to-ell order has ell-adic valuation zero, hence norm one in B by its isometric
embedding of Q_ell. The ultrametric triangle inequality bounds A by the supremum norm.
The constant average is one; left and right translations permute each finite quotient.
4. The open-normal basis separates points by clopens, so K is totally disconnected.
Apply lem-sfb-profinite-finite-map-approximation to any f and the diagonal neighbourhood
|b-c| < epsilon/2 to obtain a continuous finite-valued approximation.
5. Cover K by finitely many cosets on which that approximation is constant. Intersect
their open normal subgroups. The approximation is constant on cosets of this intersection,
so belongs to D, and its uniform error is at most epsilon/2. Thus D is dense.
6. Apply lem-sfb-dense-subspace-contractive-extension with scalar B, E=C(K,B), F=B, and
u=A. Completeness of B gives the contractive continuous linear extension I, agreeing with
every finite-quotient average and with the normalized constant.
7. Translation is an isometry preserving D. The uniqueness clause of the same extension
lemma identifies I composed with each left or right translation with I.
8. Define J_P(f)(p)=I(f(p,-)). At p_0, product neighbourhoods where
|f(p,h)-f(p_0,h)| < epsilon/2 have a finite subcover in the compact K direction.
Intersect the corresponding neighbourhoods of p_0. Contractivity then bounds the change
in J_P(f) by epsilon/2, proving continuity, also for empty P.
9. Evaluate at each p to obtain additivity, the C(P,B)-scalar identity, and finite sums,
including the empty sum. Evaluation after any continuous P' to P gives precomposition
naturality. All universes are explicit, as in def-weil-size-convention. -/
theorem primeToEll_completeScalar_integral
    (ell : ℕ) [Fact ell.Prime]
    (B : Type v) [NormedField B] [CompleteSpace B]
    (iota : Padic ell →+* B) (hiota : Isometry iota)
    (hultra : ∀ x y : B, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    (hbasis : ∀ V : Set K, IsOpen V → (1 : K) ∈ V →
      ∃ U : OpenNormalSubgroup K, (U : Set K) ⊆ V)
    (hprime : ∀ U : OpenNormalSubgroup K, Nat.Coprime (Nat.card (K ⧸ U.toSubgroup)) ell) :
    ∃ I : C(K, B) →L[B] B,
      (∀ f : C(K, B), ‖I f‖ ≤ ‖f‖) ∧
      I 1 = 1 ∧
      (∀ (a : K) (f : C(K, B)),
        I (f.comp ⟨fun h ↦ a * h, continuous_const.mul continuous_id⟩) = I f ∧
        I (f.comp ⟨fun h ↦ h * a, continuous_id.mul continuous_const⟩) = I f) ∧
      (∀ (U : OpenNormalSubgroup K) (g : K ⧸ U.toSubgroup → B) (f : C(K, B)),
        (∀ h : K, f h = g (QuotientGroup.mk h)) →
        I f = (Nat.card (K ⧸ U.toSubgroup) : B)⁻¹ * ∑' q, g q) ∧
      ∃ J : (P : Profinite.{w}) → C(P × K, B) →ₗ[B] C(P, B),
        (∀ (P : Profinite.{w}) (f : C(P × K, B)) (p : P),
          J P f p = I (f.curry p)) ∧
        (∀ (P : Profinite.{w}) (c : C(P, B)) (f : C(P × K, B)),
          J P ((c.comp ContinuousMap.fst) * f) = c * J P f) ∧
        (∀ (P P' : Profinite.{w}) (a : C(P', P)) (f : C(P × K, B)),
          J P' (f.comp (a.prodMap (ContinuousMap.id K))) = (J P f).comp a) ∧
        (∀ (P : Profinite.{w}) (n : ℕ) (f : Fin n → C(P × K, B)),
          J P (∑ j, f j) = ∑ j, J P (f j)) := by
  classical
  let : Algebra (Padic ell) B := iota.toAlgebra
  let : NormedAlgebra (Padic ell) B :=
    { norm_smul_le := fun r x ↦ by
        change ‖iota r * x‖ ≤ ‖r‖ * ‖x‖
        rw [norm_mul, hiota.norm_map_of_map_zero iota.map_zero] }
  obtain ⟨hfinite, D, hD, hconst, A, hformula, _hrefine, hbound, hone, htrans⟩ :=
    ContinuousMap.exists_finiteQuotientContractiveAverage ell B hultra K hbasis hprime
  have hdense : DenseRange D.subtype := by
    apply denseRange_subtype_val.mpr
    simpa only [← hD] using
      (ContinuousMap.openNormalQuotientFunctions_dense.{u, v, 0} K B hbasis).2.2.2
  have hbound' (f : D) : ‖A f‖ ≤ 1 * ‖D.subtype f‖ := by
    simpa only [one_mul, Submodule.subtype_apply] using hbound f
  let I : C(K, B) →L[B] B := A.extendOfNorm D.subtype
  have hagree (f : D) : I (f : C(K, B)) = A f :=
    A.extendOfNorm_eq hdense ⟨1, hbound'⟩ f
  have hI (f : C(K, B)) : ‖I f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using A.norm_extendOfNorm_apply_le hdense 1 hbound' f
  refine ⟨I, hI, ?_, ?_, ?_, ?_⟩
  · have hmem : (1 : C(K, B)) ∈ D := hconst 1
    exact (hagree ⟨1, hmem⟩).trans (hone ⟨1, hmem⟩ rfl)
  · intro a f
    let l : C(K, K) := ⟨fun h ↦ a * h, continuous_const.mul continuous_id⟩
    let r : C(K, K) := ⟨fun h ↦ h * a, continuous_id.mul continuous_const⟩
    have heqL : I.comp (l.compCLM B B) = I := by
      apply ContinuousLinearMap.ext
      apply congr_fun (hdense.equalizer
        (I.continuous.comp (l.compCLM B B).continuous) I.continuous ?_)
      funext d
      obtain ⟨dL, dR, hdL, _hdR, hAL, _hAR⟩ := htrans a d
      have heq : (d : C(K, B)).comp l = (dL : C(K, B)) :=
        ContinuousMap.ext fun h ↦ (hdL h).symm
      change I ((d : C(K, B)).comp l) = I (d : C(K, B))
      rw [heq, hagree, hagree, hAL]
    have heqR : I.comp (r.compCLM B B) = I := by
      apply ContinuousLinearMap.ext
      apply congr_fun (hdense.equalizer
        (I.continuous.comp (r.compCLM B B).continuous) I.continuous ?_)
      funext d
      obtain ⟨dL, dR, _hdL, hdR, _hAL, hAR⟩ := htrans a d
      have heq : (d : C(K, B)).comp r = (dR : C(K, B)) :=
        ContinuousMap.ext fun h ↦ (hdR h).symm
      change I ((d : C(K, B)).comp r) = I (d : C(K, B))
      rw [heq, hagree, hagree, hAR]
    exact ⟨DFunLike.congr_fun heqL f, DFunLike.congr_fun heqR f⟩
  · intro U g f hf
    let : Finite (K ⧸ U.toSubgroup) := (hfinite U).1
    let := Fintype.ofFinite (K ⧸ U.toSubgroup)
    have hmem : f ∈ D := (hD f).mpr ⟨U, g, hf⟩
    rw [hagree ⟨f, hmem⟩, hformula ⟨f, hmem⟩ U g hf]
    simp only [finsum_eq_sum_of_fintype, tsum_fintype]
  · obtain ⟨J, hJ, _hestimate, hscalar, hsum, hnatural⟩ :=
      ContinuousMap.exists_compactParameterFunctional B K I.toLinearMap hI
    exact ⟨J, hJ, hscalar, hnatural, fun P n f ↦ hsum P (Fin n) f⟩

end WeilConjectures
