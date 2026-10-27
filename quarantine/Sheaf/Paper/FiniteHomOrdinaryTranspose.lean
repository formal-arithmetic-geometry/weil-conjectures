/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import Sheaf.Paper.InternalAdjunctionPairingChange
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The ordinary coordinates of the finite coefficient Hom transpose
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-ordinary-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The right-tensor closed transpose is the published ordinary left-tensor transpose.
Source: blueprint thm-coef-finite-hom, proof paragraphs 1--2, the sentence defining v
as the transpose of reduced evaluation
(blueprint: lem-coef-finite-hom-ordinary-transpose).

Proof: the normalization of finiteHomEtaleData identifies its closed record with
finiteHomEtaleClosedGeneral and its tensorator with ExceptionalCoefficients.tensorIso.
The closed-record normalization identifies its right-tensor adjunction with the
ordinary derived tensor-Hom adjunction transported through the Koszul symmetry.
The ordinary scalar tensor comparison is the inverse of that tensorator, by uniqueness
of its flat-term K-flat representative normalization. Its signed symmetry square
moves the Koszul interchange through scalar extension. Thus both arrows, when
untransposed along the ordinary left-tensor adjunction, are the ordinary scalar
tensor comparison followed by scalar extension of its evaluation counit.
Injectivity of this adjunction's Hom equivalence gives the stated equality. This
equality is recorded in Arrow so the endpoint data are included without a costly
implicit conversion. The argument uses arbitrary objects, includes zero objects
and identity quotients,
and does not assert invertibility of either Hom comparison. -/
theorem finiteHom_ordinary_transpose
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n) :
    Arrow.mk (etaleFiniteHomCanonical l E X h K M) =
      Arrow.mk (Etale.CoefficientPairingChange.evaluationComparison
        (finiteHomQuotient l E h) X K M) := by
  sorry

end WeilConjectures
