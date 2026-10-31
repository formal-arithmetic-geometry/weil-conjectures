/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData

/-! # A step in normalized strict compactification comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluation of the normalized open and complete compactification words.
Source: blueprint operations proof (2), expanded steps 5--7; Stacks 0GL1.
(blueprint: lem-sp-strict-open-word-evaluation).

Proof: apply openTensorNormalization to the sequence-site open square. The inverse
open comparison is the transpose of pullback of the open unit followed by the
pullback compositor, so it defines OpenExchange with its required mate equation.
At every finite coefficient level use the same construction. The tensor pullback
map is the transported generic levelTensorPullback; its HEq normalization follows
from Geometry.coefficients, target, and the constant-section inverse-image model.
The resulting open tensor and exchange inverses satisfy the displayed finite
transpose equations. These determine the maps by the adjunction bijections.
Naturality of the proper projection transpose, of open tensor, and of the
pullback compositor proves projection naturality. Evaluate the proper transpose
using the unit and counit evaluation equations of the geometric calculus. Evaluate
the open tensor map using its inverse-transpose characterization and the same open
adjunction equations; compose with Operations.comp_evaluation. This is exactly the
finite proper-counit/open-tensor/compositor word in comparisonLevelProjection.
For exchange, apply evaluation_mate to the proper pullback square, using the same
comp_evaluation for its square. Follow this by the evaluated open exchange. The
result is the identical finite unit--square--counit--open word, hence the stated
exchange equation. All equations compare actual maps; joint conservativity is
never used to infer equality of derived morphisms. -/
theorem strictOpenWordEvaluation (b : Base l E) (o : Operations l E b)
    (hsystem : StrictSystemComparisons l E b o) :
    ∃ x : OpenExchange l E b o, ∃ levels : ComparisonLevels l E b o,
      StrictWordComparisons l E b o x levels := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
