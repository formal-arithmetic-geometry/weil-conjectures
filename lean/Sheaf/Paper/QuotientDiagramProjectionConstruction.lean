/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientDiagramProjectionData

/-! # Construction of quotient reduction presentations

The ordinary quotient and tensor units determine the derived comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections
namespace SheafOfModules.QuotientDiagramProjection
variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} X]

/-- Canonical ordinary and derived quotient reductions and their geometric comparison.
Source: Stacks, sites-cohomology.tex, lemma-pullback-tensor-product (07A4),
lemma-adjoint (07A6); Zheng Construction 4.1 and the singleton comparison before 4.10.
(blueprint: lem-pur-quotient-diagram-projection-construction).

Proof: take the algebraic inverse image on ring sheaves, with its induced module
adjunction. Realize ordinary quotient systems on the vertical sequence site. For
an ambient module M their components are M tensor A/(I^(n+1)); the transitions
are induced by quotienting the coefficient factor. The scalar extension units
send x to x tensor 1, hence give transition_unit, including equal indices.
Apply the same construction to the inverse-image rings. Derive the diagonal
followed by extension to the system ring, using flat-term K-flat resolutions;
its universal computation map supplies Reduction.epsilon and universal. Exact
evaluation and scalar extension compute on these same resolutions, so their
comparison gives evaluation_model. Scalar tensor balancing multiplies the two
coefficient factors. Its ordinary comparison and total-degree summand map give
TensorReduction.ordinary, summand and representative. Extension of a flat
module remains flat over the target ring; apply flat ringed-topos pullback
on the sequence site to obtain TensorReduction.flatTerms. Inverse image commutes
with this construction: both maps on scalar units insert 1, which gives
ordinaryPull_insertion. Its localization on the common resolutions gives
pull_representative. The inverse-image quotient maps respect transitions by
functoriality. Finally use the normalized singleton/geometric comparisons to
identify evaluation of direct image with the level direct images; their
counit equations and compatibility with lower-singleton maps give the
pull transition formula. The push transition formula follows by adjunction.
This constructs presentation data, independently of the
coefficient projection arrow and of the formula for its evaluation. -/
theorem quotientDiagramProjectionConstruction
    (J : GrothendieckTopology C) (K : GrothendieckTopology X)
    (A : Type (max c v r)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf K (Type (max c v r)))
    (uPush : Sheaf K (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    ∃ p : Presentation.{c, v, r} J K A I uInv uPush adj,
      p.quotient.PullTransitionFormula J (finite.{c, v, r} J A I)
        (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj := by
  sorry

end SheafOfModules.QuotientDiagramProjection
