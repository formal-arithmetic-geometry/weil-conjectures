module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Weighted coordinate formal adjoints

Source: agent-written coordinate calculation underlying Kong, Notes on Complex Geometry,
§6.1, Lemmas 6.2–6.3 (blueprint: lem-sfb-coordinate-weighted-adjoint).

The explicit variable-matrix formula is the DAG's coordinate input, rather than a formula
printed in Kong. Functions on the open domain are represented by arbitrary ambient extensions;
all smoothness, equalities and integrals are restricted to that domain. A compact set inside
the domain containing its nonzero locus expresses compact support without any condition on
the extension outside the domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff ComplexOrder

namespace CoordinateDifferentialOperator

/-- The coordinate expression `Lu = ∑ A_j ∂_j u + Bu`, with real derivatives.
Source: the local calculation supporting Kong §6.1, Lemmas 6.2–6.3
(blueprint: lem-sfb-coordinate-weighted-adjoint). -/
def firstOrder {m r s : ℕ}
    (A : Fin m → (Fin m → ℝ) → Matrix (Fin s) (Fin r) ℂ)
    (B : (Fin m → ℝ) → Matrix (Fin s) (Fin r) ℂ)
    (u : (Fin m → ℝ) → Fin r → ℂ) (x : Fin m → ℝ) : Fin s → ℂ :=
  (∑ j : Fin m, (A j x).mulVec (fderiv ℝ u x (Pi.single j 1))) + (B x).mulVec (u x)

/-- The canonical weighted adjoint expression
`Qv = (ρH_E)⁻¹ (-∑ ∂_j(ρA_jᴴH_Fv) + ρBᴴH_Fv)`.
Source: the local calculation supporting Kong §6.1, Lemmas 6.2–6.3
(blueprint: lem-sfb-coordinate-weighted-adjoint). -/
def weightedAdjoint {m r s : ℕ}
    (H_E : (Fin m → ℝ) → Matrix (Fin r) (Fin r) ℂ)
    (H_F : (Fin m → ℝ) → Matrix (Fin s) (Fin s) ℂ)
    (ρ : (Fin m → ℝ) → ℝ)
    (A : Fin m → (Fin m → ℝ) → Matrix (Fin s) (Fin r) ℂ)
    (B : (Fin m → ℝ) → Matrix (Fin s) (Fin r) ℂ)
    (v : (Fin m → ℝ) → Fin s → ℂ) (x : Fin m → ℝ) : Fin r → ℂ :=
  (((ρ x : ℂ) • H_E x)⁻¹).mulVec
    (-(∑ j : Fin m, fderiv ℝ
      (fun y ↦ (ρ y : ℂ) • (((A j y).conjTranspose * H_F y).mulVec (v y)))
      x (Pi.single j 1)) +
      (ρ x : ℂ) • (((B x).conjTranspose * H_F x).mulVec (v x)))

/-- The displayed weighted adjoint is first order with smooth coefficients, complex-linear
on smooth sections, and satisfies the weighted integration-by-parts identity if either
section has compact support inside the open coordinate domain.
Source: agent-written coordinate calculation supporting Kong §6.1, Lemmas 6.2–6.3
(blueprint: lem-sfb-coordinate-weighted-adjoint).

Proof plan:
1. Set M = ρH_E. Positivity makes M invertible. The cofactor formula and
   `lem-sfb-smooth-nonzero-complex-reciprocal` show that M⁻¹ has smooth entries.
2. Put C_j = ρA_jᴴH_F and D = ρBᴴH_F. The product rule expands Q as
   ∑ (-M⁻¹C_j)∂_j + M⁻¹(D - ∑ ∂_j C_j). These coefficients are smooth;
   matrix multiplication and real differentiation of smooth sections are complex-linear.
3. For each j and component a, zero-extend conjugate(u_a) and (C_j v)_a.
   If u has compact support K inside U, the first extension is globally smooth and the
   second is smooth near K. If v has compact support, the second is globally smooth
   and the first is smooth near its support. In both cases the derivatives are needed
   only on the other factor's closed support. Their products and derivative products
   are continuous zero extensions supported in K.
4. Apply `lem-sfb-continuous-compact-support-integrable` to these products, then
   `lem-sfb-scalar-integrable-integration-by-parts` in direction Pi.single j 1.
   Real differentiation commutes with conjugation. Reverse the resulting equality.
5. Sum over components and coordinates and add the zero-order terms. Every summand
   is integrable by step 4. The resulting right-hand vector is MQv = ρH_EQv,
   yielding the stated identity, in each of the two compact-support cases.
-/
theorem weightedAdjoint_spec {m r s : ℕ}
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U)
    (H_E : (Fin m → ℝ) → Matrix (Fin r) (Fin r) ℂ)
    (H_F : (Fin m → ℝ) → Matrix (Fin s) (Fin s) ℂ)
    (ρ : (Fin m → ℝ) → ℝ)
    (A : Fin m → (Fin m → ℝ) → Matrix (Fin s) (Fin r) ℂ)
    (B : (Fin m → ℝ) → Matrix (Fin s) (Fin r) ℂ)
    (hE : ∀ i j : Fin r, ContDiffOn ℝ ∞ (fun x ↦ H_E x i j) U)
    (hF : ∀ i j : Fin s, ContDiffOn ℝ ∞ (fun x ↦ H_F x i j) U)
    (hρ : ContDiffOn ℝ ∞ ρ U)
    (hEpos : ∀ x ∈ U, (H_E x).PosDef) (hFpos : ∀ x ∈ U, (H_F x).PosDef)
    (hρpos : ∀ x ∈ U, 0 < ρ x)
    (hA : ∀ (j : Fin m) (a : Fin s) (b : Fin r),
      ContDiffOn ℝ ∞ (fun x ↦ A j x a b) U)
    (hB : ∀ (a : Fin s) (b : Fin r), ContDiffOn ℝ ∞ (fun x ↦ B x a b) U) :
    (∃ (C : Fin m → (Fin m → ℝ) → Matrix (Fin r) (Fin s) ℂ)
        (D : (Fin m → ℝ) → Matrix (Fin r) (Fin s) ℂ),
      (∀ (j : Fin m) (a : Fin r) (b : Fin s),
        ContDiffOn ℝ ∞ (fun x ↦ C j x a b) U) ∧
      (∀ (a : Fin r) (b : Fin s), ContDiffOn ℝ ∞ (fun x ↦ D x a b) U) ∧
      ∀ (v : (Fin m → ℝ) → Fin s → ℂ), ContDiffOn ℝ ∞ v U →
        ∀ x ∈ U, weightedAdjoint H_E H_F ρ A B v x = firstOrder C D v x) ∧
    (∀ (a b : ℂ) (v w : (Fin m → ℝ) → Fin s → ℂ),
      ContDiffOn ℝ ∞ v U → ContDiffOn ℝ ∞ w U → ∀ x ∈ U,
        weightedAdjoint H_E H_F ρ A B (a • v + b • w) x =
          a • weightedAdjoint H_E H_F ρ A B v x +
          b • weightedAdjoint H_E H_F ρ A B w x) ∧
    (∀ (u : (Fin m → ℝ) → Fin r → ℂ) (v : (Fin m → ℝ) → Fin s → ℂ),
      ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      ((∃ K : Set (Fin m → ℝ), IsCompact K ∧ K ⊆ U ∧
          ∀ x ∈ U, x ∉ K → u x = 0) ∨
        (∃ K : Set (Fin m → ℝ), IsCompact K ∧ K ⊆ U ∧
          ∀ x ∈ U, x ∉ K → v x = 0)) →
      (∫ x in U, (∑ i : Fin s,
        star (firstOrder A B u x i) * ((H_F x).mulVec (v x)) i) * (ρ x : ℂ)) =
      ∫ x in U, (∑ i : Fin r,
        star (u x i) * ((H_E x).mulVec (weightedAdjoint H_E H_F ρ A B v x)) i) *
          (ρ x : ℂ)) := by
  sorry

end CoordinateDifferentialOperator
