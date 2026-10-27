/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.EulerTwistCoordinateDifference
import Sheaf.Algebra.MvPolynomial.CoordinateDifferences
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre
import Mathlib.Tactic

/-! # Snapper's numerical polynomial for several invertible twists

Source: Stacks Project, Varieties, Lemma 33.45.1, Tag 0BEM, in Section 0BEL
(blueprint: lem-sc-snapper-numerical-polynomial).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem zero_dim_fold (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (s : List X.Modules) (hs : ∀ N ∈ s, N.IsInvertible) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hd : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤ 0) :
    (s.foldl (fun M N : X.Modules ↦ M ⊗ N) F).eulerChar k = F.eulerChar k := by
  induction s generalizing F with
  | nil => rfl
  | cons N s ih =>
    have : N.IsInvertible := hs N (by simp)
    obtain ⟨hc, hsup, he⟩ := (eulerChar_zero_dim_support k X F hF hd).2.2.2 N
    exact (ih (fun N hN ↦ hs N (by simp [hN])) (F ⊗ N) hc
      (by rw [hsup]; exact hd)).trans he

private theorem invertible_integer_factor {X : Scheme.{u}} (L : X.Modules)
    [L.IsInvertible] (n : ℤ) :
    (if 0 ≤ n then L.tensorPow n.toNat else L.dual.tensorPow (-n).toNat).IsInvertible := by
  split <;> infer_instance

private theorem zero_fold {X : Scheme.{u}} (s : List X.Modules)
    (hs : ∀ N ∈ s, N.IsInvertible) (F : X.Modules)
    (hF : CategoryTheory.Limits.IsZero F) :
    CategoryTheory.Limits.IsZero (s.foldl (fun M N : X.Modules ↦ M ⊗ N) F) := by
  induction s generalizing F with
  | nil => exact hF
  | cons N s ih =>
    have : N.IsInvertible := hs N (by simp)
    have := isEquivalence_tensorRight N
    exact ih (fun N hN ↦ hs N (by simp [hN])) (F ⊗ N)
      ((tensorRight N).map_isZero hF)

private theorem bounded_euler_polynomial
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (d : ℕ) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hd : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤
      (d : WithBot ℕ∞))
    (r : ℕ) (L : Fin r → X.Modules) [∀ i : Fin r, (L i).IsInvertible] :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ d ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun i ↦ (n i : ℚ)) P =
        (((List.ofFn fun i : Fin r ↦
          if 0 ≤ n i then (L i).tensorPow (n i).toNat
          else (L i).dual.tensorPow (-n i).toNat).foldl
            (fun M N : X.Modules ↦ M ⊗ N) F).eulerChar k : ℚ) := by
  classical
  induction d generalizing F with
  | zero =>
    refine ⟨MvPolynomial.C (F.eulerChar k : ℚ),
      (MvPolynomial.totalDegree_C _).le, fun n ↦ ?_⟩
    rw [MvPolynomial.eval_C]
    congr 1
    symm
    apply zero_dim_fold k X _ _ F hF hd
    intro N hN
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hN
    exact invertible_integer_factor (L i) (n i)
  | succ d ih =>
    apply MvPolynomial.exists_eval_eq_of_coordinate_differences r (d + 1)
    intro j
    obtain ⟨m, G, c, hG, hdim, he⟩ :=
      eulerChar_tensorPowers_coordinate_difference k X F hF d hd r L j
    choose P hP heP using fun a ↦ ih (G a) (hG a) (hdim a)
    refine ⟨∑ a : Fin m, MvPolynomial.C (c a : ℚ) * P a, Or.inr ?_, fun n ↦ ?_⟩
    · apply Nat.lt_succ_of_le
      apply MvPolynomial.totalDegree_finsetSum_le
      intro a ha
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact hP a)
    · simp only [map_sum, map_mul, MvPolynomial.eval_C, heP]
      exact_mod_cast he n

/-- The Euler characteristic of a coherent module twisted by integer powers of finitely
many invertible modules is a rational polynomial, integer-valued on the integer lattice,
of total degree at most the dimension of the coherent module's support.
Source: Stacks Project, Varieties, Lemma 33.45.1, Tag 0BEM
(blueprint: lem-sc-snapper-numerical-polynomial).

Integer powers use `tensorPow` for nonnegative exponents and powers of `dual` for negative
exponents. The list fold starts at `F` and tensors the factors in their given order.
The support is the subspace of points with nonzero stalk. The zero polynomial has degree
minus infinity, expressed separately because `MvPolynomial.totalDegree 0 = 0`.

Proof (for stage 3):
1. Induct on the support dimension. In dimension zero, invertible twists preserve Euler
   characteristic by `lem-pc-chi-zero-dim-support`, giving a constant polynomial. The zero
   sheaf, including the case of an empty scheme, gives the zero polynomial.
2. Remove embedded associated points using `lem-sc-hilbert-embedded-points`. Its kernel has
   smaller support dimension, so `lem-pc-euler-additive` reduces to the quotient. Use
   `lem-weil-pbc-scheme-theoretic-support` and
   `lem-weil-pbc-closed-immersion-coherent-equivalence` to write the quotient as a direct
   image from its scheme-theoretic support; `lem-pc-closed-immersion-coherent-cohomology`
   preserves the twisted Euler characteristics. Faithfulness embeds the structure sheaf
   locally into a finite sum of copies of the module, so its associated points are among
   those of the module. Thus the support scheme has no embedded points.
3. For each coordinate, `lem-sc-regular-meromorphic-section-exists` supplies a regular
   meromorphic section. Apply `lem-sc-hilbert-difference` to the quotient twisted by the
   other factors. Its forward difference is a difference of Euler characteristics of
   coherent modules of strictly smaller support dimension.
4. Induction makes every first difference a numerical polynomial of degree at most d-1.
   The arithmetic argument of Tag 0BEM integrates coordinate differences, fixing the
   constant on the zero slice, and repeats on the remaining slice. It produces a rational
   polynomial of total degree at most d on the entire integer lattice.
5. Add the smaller-degree kernel contribution by `lem-pc-euler-additive` to obtain the
   asserted bound for the original module. -/
theorem exists_mvPolynomial_eulerChar_tensorPowers
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (r : ℕ) (L : Fin r → X.Modules) [∀ i : Fin r, (L i).IsInvertible] :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ ((P.totalDegree : ℕ∞) : WithBot ℕ∞) ≤
        topologicalKrullDim
          {x : X | ¬ Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf x)}) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun i => (n i : ℚ)) P =
        (((List.ofFn fun i : Fin r =>
          if 0 ≤ n i then (L i).tensorPow (n i).toNat
          else (L i).dual.tensorPow (-n i).toNat).foldl
            (fun M N : X.Modules => M ⊗ N) F).eulerChar k : ℚ) := by
  classical
  let S := {x : X | ¬ Subsingleton (F.presheaf.stalk x)}
  have hbound : topologicalKrullDim S ≤
      (((topologicalKrullDim X).unbotD 0).toNat : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le X S).trans (topologicalKrullDim_le_unbotD_toNat k)
  by_cases hb : topologicalKrullDim S = ⊥
  · have hempty : IsEmpty S := by
      have hi : IsEmpty (TopologicalSpace.IrreducibleCloseds S) :=
        Order.krullDim_eq_bot_iff.mp hb
      refine ⟨fun x ↦ hi.false
        ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have hzero : CategoryTheory.Limits.IsZero F := by
      apply isZero_of_isZero_stalk
      intro x
      have : Subsingleton (F.presheaf.stalk x) := by
        by_contra hx
        exact hempty.false ⟨x, hx⟩
      exact AddCommGrpCat.isZero_of_subsingleton _
    refine ⟨0, Or.inl rfl, fun n ↦ ?_⟩
    rw [map_zero]
    have he := eulerChar_eq_zero_of_isZero k (zero_fold _ (by
      intro N hN
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hN
      exact invertible_integer_factor (L i) (n i)) F hzero)
    rw [he, Int.cast_zero]
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim S = (d : WithBot ℕ∞) := by
      generalize hh : topologicalKrullDim S = D at *
      cases D using WithBot.recBotCoe with
      | bot => exact (hb rfl).elim
      | coe D =>
        cases D using ENat.recTopCoe with
        | top =>
          have ht := hbound
          change (⊤ : WithBot ℕ∞) ≤ _ at ht
          have hn := (WithBot.coe_le_coe.mp ht)
          exact (ENat.natCast_ne_top _ (top_le_iff.mp hn)).elim
        | coe d => exact ⟨d, rfl⟩
    obtain ⟨P, hP, he⟩ := bounded_euler_polynomial k X d F hF hd.le r L
    refine ⟨P, Or.inr ?_, he⟩
    change _ ≤ topologicalKrullDim S
    rw [hd]
    exact_mod_cast hP

end AlgebraicGeometry.Scheme.Modules
