/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare

/-!
# Direct-image exchange for finite constant coefficients

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-star-exchange.md (blueprint: pur713-def-star-exchange).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/--
The direct-image exchange for a Cartesian square with finite constant coefficients.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-star-exchange.md (blueprint: pur713-def-star-exchange).
Proof: the component at `K` is the mate, under the normalized derived adjunction for
`f'`, of the canonical pullback comparison followed by the pullback of the counit for
`f`. The mate construction gives a natural transformation and no invertibility claim.
-/
noncomputable def proEtaleFiniteCoefficientDirectImageExchange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    proEtaleRingDerivedDirectImage f
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))
        (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E n)) ⋙
        proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E n) g ⟶
      proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E n) g' ⋙
        proEtaleRingDerivedDirectImage f'
          (proEtaleConstantRing Y' (Padic.coefficientExtensionRing l E n))
          (proEtaleConstantRing X' (Padic.coefficientExtensionRing l E n))
          (proEtaleConstantRingComparison f' (Padic.coefficientExtensionRing l E n)) :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction f
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))
      (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E n)))
    (proEtaleRingDerivedAdjunction f'
      (proEtaleConstantRing Y' (Padic.coefficientExtensionRing l E n))
      (proEtaleConstantRing X' (Padic.coefficientExtensionRing l E n))
      (proEtaleConstantRingComparison f' (Padic.coefficientExtensionRing l E n)))
    (TwoSquare.mk _ _ _ _
      (proEtaleConstantRingPullbackComparison l E n _hn sq).hom)).natTrans

end AlgebraicGeometry.Scheme

end
