/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedCompleteOnSlices

/-!
# The normalized quotient-completion unit on complete objects

Source: Bhatt--Scholze, Proposition 3.5.1 and Definition 3.5.2.
(blueprint: lem-sf-integral-completion-unit-criterion).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory
namespace WeilConjectures.IntegralOnSlice

/-- The specified quotient-completion unit is invertible on derived-complete objects.
Source: Bhatt--Scholze, Proposition 3.5.1 and Definition 3.5.2
(blueprint: lem-sf-integral-completion-unit-criterion).

Proof: choose a flat-term K-flat representative P of C. The identity coefficient
extension in finiteFreeCompletedScalarComparison computes the canonical completion
map of P, with quotient components x mapped to 1 tensor x and zero second cone
component. The quotient projections of IntegralOnSlice are the same completed-ring
projections. The universal property of ordinary scalar extension gives the unique
comparison between each of its chosen reduction functors and the identity-extension
reduction functor. These comparisons send a tensor x to a tensor x, commute with
quotient transitions, and carry the augmentation to the augmentation. Their products
and mapping cocones therefore give an isomorphism of the two Roos complexes. The
identity multiplication isomorphism and the final identity equation of the finite-free
comparison theorem identify its chain comparison with roosUnit P: both are (c,0).
The theorem makes its localization invertible when C is complete. The defining
equation of completionUnit identifies it, after completionComparison, with this
localized roosUnit. Hence completionUnit is invertible at Q(P). Finally its naturality
along the representative isomorphism Q(P) ≅ C gives invertibility at C. This uses
neither boundedness nor constructibility, and the zero object is included. -/
theorem integralCompletionUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (C : D l E X none)
    (hC : IsComplete l E X none C) :
    IsIso ((completionUnit l E X none).app C) := by sorry

end WeilConjectures.IntegralOnSlice
