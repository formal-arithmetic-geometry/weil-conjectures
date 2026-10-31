/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProductFactors

/-! Proper normalization and coefficient compatibility for relative-product factors.

Source: proper-replacement and proper-coefficient paragraphs
(blueprint: lem-sf-relative-product-coefficient-factor-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Proper replacements preserve the normalized factor equations and their
coefficient comparisons.
Source: proper-replacement and proper-coefficient proof steps 6--8
(blueprint: lem-sf-relative-product-coefficient-factor-squares).

Proof: insert the specified proper identifications at every support occurrence,
including nested occurrences and the two coefficient presentations.  Naturality
of tensor, support, and the supplied proper adjunction comparisons identifies the
conjugated projection and exchange maps with the direct-image normalizations.
Conjugating each of the six coefficient squares by these identifications gives
`ProperFactorSquares` and the two normalization predicates.
-/
theorem relative_product_proper_compatibility_core
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R')
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :
    ∀ (J : RelativeProductProperCoordinates R.coordinates)
      (J' : RelativeProductProperCoordinates R'.coordinates),
      R.ProperNormalization J ∧ R'.ProperNormalization J' ∧
        A.ProperComparisonNormalization J J' ∧ A.ProperFactorSquares J J' cg ch := by
  sorry

end WeilConjectures
