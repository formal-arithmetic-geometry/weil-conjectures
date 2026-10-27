/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.ClassicalFiniteWeilDiagramData

/-! # Coherent normalized finite stages for a supplied classical realization

Source: BS 6.8.4(1),(4), 6.8.14(2), Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u v w z
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor (IsoAlgebra)
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

variable [Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- Choose coherent normalized finite witnesses without changing the supplied realization.
Source: Bhatt--Scholze 6.8.4(1),(4), 6.8.14(2), Remark 6.8.15;
finite Weil-diagram proof steps 4--6 and 8.
(blueprint: lem-zl-coherent-normalized-diagram-stages).

Proof: choose a normalized lisse realization Family using lisse_rational_realization.
For each finite field take the witness supplied by R.pullback_pinning. Its integral
completion comparison is fixed on all finite quotient projections, and its localization
comparison on the localization unit. The chosen Family has these same normalizations.
Thus the integral comparison and the fraction formula give a natural linear isomorphism
between the two ordinary module realizations. Transport the witness's sheaf comparison
along it and use the chosen Family's realization and Along fields. PullNormalized makes
the ordinary comparisons equal on integral tensors; linearity and localization extend
this to the rational maps. This proves ordinary_unit; finite_unit, finite_pullback,
stage and the equality pinning R.pullback retain their original witnesses. The completed
rational Hom bijection, sheaf_linear and the lisse-heart Hom bijection prove full
faithfulness of finite, and their fraction formulas prove finite_add. The raw pullback
map rule and finite_unit give the classical natural isomorphism, whose components are
the equalities classical_objects. Finally use the Family's normalized field-change
comparisons for the coefficient coherence. No diagram, lattice, or object is chosen by
this theorem, and every stage remains pinned to the input R. -/
theorem zl_coherent_normalized_diagram_stages
    (R : ZlClassicalRealization D l hl Ω Y₀) :
    ∃ P₀ : ∀ E : Padic.FiniteCoefficientFields l Ω, ZlDiagramStage D l hl Ω Y₀ R E,
      ZlDiagramCoefficientCoherence D l hl Ω Y₀ R P₀ := by sorry

end WeilConjectures
