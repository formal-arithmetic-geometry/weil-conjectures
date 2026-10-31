/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportBaseChangeOfPreserves
public import WeilConjectures.AlgebraicGeometry.ProperBaseChangeRationalPushforward
import WeilConjectures.AlgebraicGeometry.ProperBaseChangeRationalExchange

/-!
# The proper step of compact-support base change

Source: literature/blueprint/slopmaster2-20261029-1700/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-thm-sfb-shriek-base-change-proper-step.md, node
(blueprint: det-thm-sfb-shriek-base-change-proper-step).

The statement records proper base change for the restricted bounded-constructible functors
and its whiskering by extension by zero. The proof uses the compactification/base-change
construction, rational proper base change, the restricted base-change formula, and the
componentwise inverse calculation described in the DAG proof steps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X X' Y Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- For a rational condensed coefficient ring, the proper base-change map of the
restricted bounded-constructible functors is invertible, as is its whiskering by the
extension-by-zero functor of a compactification.

Source: literature/blueprint/slopmaster2-20261029-1700/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-thm-sfb-shriek-base-change-proper-step.md, node
(blueprint: det-thm-sfb-shriek-base-change-proper-step).

Proof following the four DAG steps:
1. `det-def-sfb-shriek-base-change-morphism-compactification` gives the cartesian proper
square in the standing setting. The compactification definition
`sk-def-nagata-sketch-data` gives properness of the original factor. Preservation for both
coefficient fields is `lem-sfb-dc-lower-star-preserves`; the named preservation proof below
therefore supplies all the restricted pushforwards required by the situation.
2. The maps in `det-def-sfb-base-change-morphism` and its detailed `-bc` definition are the
unit, canonical pullback comparison, and counit composite. By
`det-def-sfb-dc-restricted-functors`, their images under inclusion are the ambient factors:
the restricted adjunction Hom equivalence is the same equivalence, so its unit and counit
are the ambient ones. Thus this is the canonical proper base-change map.
3. Apply clause 3 of `det-thm-sfb-proper-base-change-rational` to every bounded constructible
object on the middle scheme. The det/sk setting, coefficient and bounded-constructible
definitions specify the same rings and full subcategory, with no additional finite-Tor or
completeness condition. The inverse of the ambient map is a morphism in the full
subcategory because both endpoints belong to it. This gives invertibility there.
4. For BC : A ⟶ B, naturality says A.map(u) ≫ BC.app(L) = BC.app(K) ≫ B.map(u).
Compose with the component inverses to obtain their naturality; the two inverse identities
hold componentwise. Finally `def-sfb-dc-open-lower-shriek` supplies i_!. The whiskered
component at K is BC.app(i_! K), with the same inverse and naturality, so its two inverse
identities follow componentwise as well.
-/
theorem isIso_properBaseChangeShriekStep
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (sq : IsPullback g' f' f g)
    (c : Compactification.BoundaryCompactification f.left) :
    IsIso (boundedConstructibleBaseChangeOfPreserves Λ.X ℓ
      (rationalCoefficientPushforwardPreservation ℓ Λ hΛ)
      (c.obj.obj.overBaseChange_isPullback_g sq).toCommSq) ∧
    IsIso (Functor.whiskerLeft
      (boundedConstructibleOpenImmersionLowerShriek Λ.X ℓ c.obj.obj.overI)
      (boundedConstructibleBaseChangeOfPreserves Λ.X ℓ
        (rationalCoefficientPushforwardPreservation ℓ Λ hΛ)
        (c.obj.obj.overBaseChange_isPullback_g sq).toCommSq)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
