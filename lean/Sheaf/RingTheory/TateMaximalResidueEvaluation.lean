/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Maximal residue fields of Tate algebras and convergent evaluation

Source: Conrad, Several approaches to non-archimedean geometry, §1.1,
finite-extension paragraph, Exercise 1.1.4 and Theorem 1.1.5(1), PDF pp. 2--4
(blueprint: lem-per-tate-maximal-residue-evaluation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- The scalar inclusion into the actual maximal quotient (also defined for any ideal).
Source: Conrad, §1.1, Theorem 1.1.5(1), PDF p. 4
(blueprint: lem-per-tate-maximal-residue-evaluation). -/
noncomputable def tateResidueScalar
    (F : Type u) [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (n : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)))) :
    F →+* (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n) :=
  (Ideal.Quotient.mk n).comp (constants F r)

/-- The image of a coordinate in the actual maximal quotient.
Source: Conrad, §1.1, Exercise 1.1.4, PDF p. 3
(blueprint: lem-per-tate-maximal-residue-evaluation). -/
noncomputable def tateResidueCoordinate
    (F : Type u) [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (n : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))))
    (i : Fin r) :
    ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n :=
  Ideal.Quotient.mk n ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_monomial _ _ _⟩

/-- A maximal Tate quotient is finite over the base and has its unique complete extending
absolute value; the quotient map is the convergent evaluation at its coordinate images.
Source: Conrad, §1.1, preliminary finite-extension paragraph, Exercise 1.1.4,
Theorem 1.1.5(1), PDF pp. 2--4
(blueprint: lem-per-tate-maximal-residue-evaluation).

Proof:
1. Induct on r. With no variables the ring is F. With a variable the Tate ring is not a
field, since the last variable is nonzero and its constant coefficient is zero. Thus a
maximal ideal contains a nonzero f. Use lem-trf-restricted-series-gauss-completion for
Gauss completeness and regrouping.
2. Apply lem-per-tate-triangular-distinguished-coordinate to f. Multiplication by a unit
makes its transformed image distinguished. By lem-trf-tate-weierstrass-norm-division,
the quotient is generated over the Tate ring in one fewer variable by finitely many
powers of the last variable. Distinguished degree zero is excluded by properness.
3. Let B be the image of the smaller Tate ring in the residue field. The residue field is
finite over B and hence integral by lem-weil-pbc-finite-algebra-is-integral. An integral
equation for the inverse of a nonzero b in B shows that inverse lies in B. Thus B is a
field. Induction makes B finite over F, and products of the two finite spanning sets
prove the residue field finite over F (def-weil-finitely-generated-module).
4. The extension is algebraic. Use lem-trf-spectral-norm-algebraic-extension for the
extending ultrametric absolute value, lem-per-finite-normed-space-complete for its
completeness, and lem-sfb-algebraic-absolute-value-unique for uniqueness, also inseparably.
5. By lem-per-tate-finite-scalar-extension, scalar extension to the residue field is its
Tate algebra. The quotient character extends to that algebra via the tensor product
(def-weil-pbc-module-tensor-product). The Gauss Banach structure from
lem-trf-restricted-series-gauss-completion and lem-per-banach-character-norm-bound give
that this character is norm decreasing. Its coordinate values therefore have norm at
most one.
6. Polynomial truncations converge by lem-trf-restricted-series-gauss-completion.
The character bound makes their quotient values converge to the quotient of the series.
Each monomial value has norm at most the norm of its coefficient, so coefficient decay
and the ultrametric inequality also give unconditional convergence of the finite sums.
For r = 0 there is only the empty exponent; the maximal ideal is zero and the scalar
map identifies its quotient with F.
-/
theorem tate_maximal_residue_evaluation
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (hF : ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1) (r : ℕ)
    (n : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))))
    [n.IsMaximal] :
    @Module.Finite F _ _ _ (tateResidueScalar F r n).toAlgebra.toModule ∧
    (∃ v : AbsoluteValue
        (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n) ℝ,
      (∀ c : F, v (tateResidueScalar F r n c) = ‖c‖) ∧
      IsNonarchimedean v ∧
      @CompleteSpace _ v.toNormedRing.toUniformSpace ∧
      (∀ w : AbsoluteValue
          (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n) ℝ,
        (∀ c : F, w (tateResidueScalar F r n c) = ‖c‖) → w = v) ∧
      (∀ i : Fin r, v (tateResidueCoordinate F r n i) ≤ 1) ∧
      (∀ h : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))),
        @HasSum _ (Fin r →₀ ℕ) _ v.toNormedRing.toUniformSpace.toTopologicalSpace
          (fun ν ↦ tateResidueScalar F r n (MvPowerSeries.coeff ν h.val) *
            ν.prod (fun i e ↦ tateResidueCoordinate F r n i ^ e))
          (Ideal.Quotient.mk n h) (SummationFilter.unconditional (Fin r →₀ ℕ)))) ∧
    (r = 0 → n = ⊥ ∧ Function.Bijective (tateResidueScalar F r n)) := by
  sorry

end RestrictedSeries
