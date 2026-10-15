/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.FieldFailure
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
import Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening
import Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening
import Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp
import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent
import Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection
import Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage
import Sheaf.AlgebraicGeometry.BaseChangeClosedOpenEmbedding
import Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero
import Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients

/-!
# Detection of failure of base change over a field

Source: Stacks Project, Tag 0F07; blueprint sec-smooth-base-change,
sk-lem-failure-field (blueprint: sbc-lem-bc-failure-field).

The existing `FieldFailure` bundles the two Cartesian squares, affine base, field,
coefficient sheaf and failure of the degreewise canonical base-change map.
The coefficient ring is the size lift of `ZMod n`, so its module sheaves are precisely
abelian sheaves annihilated by `n`, as in the recorded base-change property.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Failure of universal degree-`q` base change, assuming universal base change in every
nonnegative lower degree, is witnessed over a field after an affine base change.
If the original base is separated, the same affine base has an affine structural morphism.
Source: Stacks Project, Tag 0F07; blueprint sec-smooth-base-change/sk-lem-failure-field
(blueprint: sbc-lem-bc-failure-field).

Proof plan:
1. Negate universal base change and restrict the failing square to an affine open of its
base, using `sbc-lem-etale-locality`. Quasi-compactness and quasi-separatedness persist;
the resulting horizontal source is qcqs by `lem-weil-pbc-qcqs-morphism-permanence`.
2. The critical map is injective by `sbc-lem-bc-injectivity`. Exactness and conservativity
of geometric stalks supply an element outside its image. Use the canonical stalk transitions
and `lem-weil-pbc-exchange-forget-coefficients` to work with `ZMod n`-module coefficients.
3. Define survival to mean that the transported element remains outside the image.
The source and target thickening-transition lemmas give isomorphisms. The unit/counit
mate formula shows that these transitions commute with base change; stalk transport
composition then proves thickening invariance.
4. For a cofiltered limit of qcqs schemes with affine transitions, source-image limit
descent supplies a preimage at a finite stage if the element dies at the limit. Target
limit zero detection makes the difference vanish at a later stage, and target restriction
preserves the base-change image. This contradicts survival at that stage.
5. For a closed immersion with quasi-compact open complement, embed the coefficient into
its closed restriction plus the direct image of an injective module sheaf from the open.
The open-injective coefficient-zero and closed-coefficient-range lemmas show that, if
survival fails on both pieces, its image in the enlarged coefficient cokernel is zero.
6. Additivity splits that enlarged cokernel into the two components. Naturality of the mate
identifies their maps. The cokernel injection of `sbc-lem-bc-injectivity`, preserved by
exact stalks, contradicts survival. This proves the closed-open condition.
7. On the empty scheme the target stalk is zero, so survival fails. Apply
`sbc-lem-bc-minimal-counterexample` to obtain a field and pull back the coefficient sheaf;
its failed stalk map proves that the field-square map is not an isomorphism.
8. If the original base is separated, its diagonal is a closed immersion. Pulling it back
identifies each affine-chart inverse image with a closed subscheme of a product of affine
schemes. These inverse images are affine, so the structural morphism is affine.
-/
theorem exists_fieldFailure_of_cumulativeUniversalBaseChangeProperty
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(S, ⊤))) (q : ℕ) (hq : 1 ≤ q)
    (hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1))
    (hfail : ¬ UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)) :
    ∃ d : FieldFailure (ULift.{u + 1} (ZMod n)) f (q : ℤ),
      S.IsSeparated → IsAffineHom d.a := by
  sorry

end AlgebraicGeometry.Etale
