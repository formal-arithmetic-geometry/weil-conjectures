/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison

/-! # Perfect coefficients in the strict reduction projection

Source: Stacks Project, Cohomology on Sites, Tag 0944.
(blueprint: lem-pur-perfect-reduction-projection-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace CategoryTheory.AdicSites

variable {Y X : Site.{u}} (f : Morphism Y X) (A : Type u) [CommRing A] (I : Ideal A)

/-- The projection evaluated at a single perfect positive quotient is invertible.

Source: Stacks Project, sites-cohomology.tex, Tag 0944 and equation 0B56,
with Tags 07A4 and 0941 for pullback and strict evaluation
(blueprint: lem-pur-perfect-reduction-projection-evaluation).

Proof: represent the quotient A/I^(n+1) by a bounded complex of finite projective
A-modules. Split every term off a finite free module and apply exact constant
realization. The resulting bounded finite-free retract complex represents the
constant quotient on each site and proves that this coefficient is perfect.
On flat-term K-flat representatives, evaluation of the scalar quotient reduction
is the derived tensor with this coefficient: the ordinary comparison sends the
local pure tensor s tensor m to that same pure tensor, and the universal derived
comparisons descend it. The moduleReductionPullIso insertion equation fixes the
pullback/tensor comparison; its full cochain normalization fixes reductionPullIso.
The evaluation/pushforward comparison preserves the derived counit. Transposing
the evaluated towerProjection therefore gives the counit tensored with identity,
which is exactly the ringed-site projection-formula map of equation 0B56 under
these endpoint comparisons. Apply the perfect projection formula, Tag 0944,
and conjugate by the endpoint isomorphisms. No uniform bounds, flat quotient,
completeness, or faithfulness of derived evaluation is used. For a zero quotient
both tensor objects are zero, and the same argument covers empty sites. -/
theorem perfectReductionProjectionEvaluation (n : ℕ)
    (hperfect : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (quotientRing A I n)))) (F : X.derived A) :
    IsIso ((Y.evaluate A n).map (f.towerProjection A I F)) := by
  sorry

end CategoryTheory.AdicSites
