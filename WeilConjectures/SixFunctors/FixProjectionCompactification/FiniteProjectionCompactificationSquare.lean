/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
import WeilConjectures.SixFunctors.FixProjectionCompactification.FiniteProjectionFromDescent

/-! # Finite witnessed projection comparison through a common refinement

Source: current blueprint, prop-sf-pf-coherence.proof.md, compactification-independence
sentence (blueprint: lem-sf-finite-projection-compactification-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification

/-- The finite coefficient clause with both actual origin presentations retained.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence;
lem-fix-projection-compactification-comparison, proof steps 1--6.
(blueprint: lem-sf-finite-projection-compactification-square).

The categorical cancellation is isolated in `finiteProjectionFromDescent`; this
entry specializes the refinement-law clause supplied by `finite_descent`.
-/
theorem finiteCompactificationProjection
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k)) :
    finiteLaw D C E n hn hl := by
  cases n with
  | zero => omega
  | succ n =>
    apply finiteProjectionFromDescent D C E n hn S hl
    intro X Y _ _ _ _ _ _ f _ _ _ _
    exact (ProjectionRefinementDescent.finite_descent D C E n S f).2.1

end WeilConjectures.FixProjectionCompactification
