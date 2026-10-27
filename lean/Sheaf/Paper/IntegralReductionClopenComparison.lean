/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.ClopenIntegralRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-! # Ordinary open restriction commutes with one derived integral reduction

Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks Tags 06YY and 00XZ
(blueprint: lem-pur-integral-reduction-clopen-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Derived extension to a single positive quotient commutes with ordinary open
restriction, in the published constant-ring inverse-image presentation.
This asserts neither a comparison of towers nor any augmentation, transition,
completeness or constructibility statement.

Source: Stacks Tags 06YY, 00XZ and 03CO; Bhatt--Scholze, Definition 3.5.2, p. 24;
step 2 followed by the coefficient identification in step 5 of
lem-pur-clopen-augmented-integral-descent
(blueprint: lem-pur-integral-reduction-clopen-comparison).

Proof: restriction along composition with the open immersion commutes with
sheafification and identifies the constant quotient rings by their constant sections.
It preserves the inverse limit defining the completed ring. Uniqueness against all
quotient projections identifies this completed comparison with clopenCompletionMap.
In particular the completed-to-quotient square commutes. Sheafified scalar tensor
therefore commutes with restriction: on local generators it sends s tensor x to
restricted s tensor restricted x. Its inverse uses the inverse coefficient maps.
Exact restriction preserves quasi-isomorphisms and K-flatness, so the localized
chain comparison computes the two derived extension functors on K-flat models.
The universal property of localization extends it, and its inverse, to all derived
objects and morphisms. Finally ordinary open restriction of constant-ring modules
is proEtaleConstantRingPullback by uniqueness of left adjoints to the same direct
image. Descend this last comparison termwise. The argument works on the empty site,
for the zero object, at exponent one, and for ramified extensions, since no flatness
of the quotient map is used. -/
theorem integralReductionClopenComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Nonempty (scalarReductionDerivedExtension l E X n ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) j ≅
      clopenIntegralDerivedRestriction l E j ⋙ scalarReductionDerivedExtension l E Y n) :=
  by sorry

end WeilConjectures.PurityFiniteSetting
