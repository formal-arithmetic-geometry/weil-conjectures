/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.Paper.A1FiniteWeilSectionsDecomposition

/-! # Weights of the cohomology of a finite boundary

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
lem-a1-finite-boundary-weights (blueprint: lem-a1-finite-boundary-weights).

The degree-zero compact-support image is retained in the actual common-stage
Weil heart on Spec(k₀). Its geometric fibre is H_c⁰ with its induced Frobenius.
At this point the punctual mixed-weight filtration is exactly the mixed-weight
filtration of that finite-dimensional Frobenius module. The proper map itself
is its compactification, so no auxiliary compactification hypothesis is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The geometric compactly supported degree-zero cohomology of a finite k₀-scheme
has weights at most w when every local stalk eigenvalue has that bound, normalized
by the cardinality of its residue field. The conclusion uses the canonical
compact-support image as a Weil sheaf on Spec(k₀), equivalently its geometric
coefficient fibre with global q-Frobenius.

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
lem-a1-finite-boundary-weights (blueprint: lem-a1-finite-boundary-weights).
Proof:
1. Apply lem-a1-finite-weil-sections-decomposition. Evaluation identifies geometric
   H_c⁰ with the finite sum of geometric stalks. For a closed point of degree d,
   evaluation intertwines the d-th power of global Frobenius with local Frobenius.
2. The hypothesis gives the local eigenvalue bound with base q^d. If stalk weights
   are presented by a mixed filtration, p-linear-filtration gives this same bound
   from the pure successive quotients, including the zero-stalk case.
3. A nonzero eigenvector v for global Frobenius has a nonzero stalk component.
   Its local return eigenvalue is λ^d. Hence |iota(λ)|^d ≤ (q^(w/2))^d;
   since d ≥ 1, taking the increasing d-th root gives |iota(λ)| ≤ q^(w/2).
4. Apply lem-a1-punctual-bound-module-mixed to the finite-dimensional global
   Frobenius module. Under the geometric-point fibre equivalence, its stable
   filtration is precisely the displayed mixed filtration in the Weil heart
   of Spec(k₀). The empty scheme gives the length-zero filtration. -/
theorem sf_finiteBoundary_hasWeightsAtMost
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] (iota : Qbar ≃+* ℂ)
    (Z₀ : Over (Spec (.of D.k₀))) [IsFinite Z₀.hom]
    (G : sfCommonStageWeilSheaf D l hl Z₀ Qbar) (w : ℝ)
    (hG : ∀ (y : {y : Z₀.left // y ∈ closedPoints Z₀.left}) (α : Qbar),
      SfPunctualEigenvalue D l hl Qbar Z₀ G y α →
        ‖iota α‖ ≤ (Nat.card (Z₀.left.residueField y.val) : ℝ) ^ (w / 2)) :
    SfIsMixedOfWeightsAtMost D l hl Qbar (sfWeilCohomologyPoint D) iota
      (commonStageCompactWeilCohomology D l hl Qbar Z₀
        (Compactification.ofIsProper Z₀.hom) G 0) w := by
  sorry

end WeilConjectures
