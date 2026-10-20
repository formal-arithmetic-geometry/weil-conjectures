/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Base change for one normalized finite reduction

The finite constant-sheaf identifications and the adjunction-mate calculation for a
single continuous finite quotient. This calculation is independent of the integral
limit and of its ring-compatible comparison.

Source: blueprint main-20261015, coefficient pullback proof, second paragraph
(blueprint: lem-sfb-finite-reduction-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison between a constant commutative ring sheaf, regarded as
an abelian sheaf, and the constant abelian sheaf of its additive group.
Source: blueprint pullback clause 1, canonical finite constant-sheaf identifications
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def sfbConstantRingAbIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of A) :=
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A) ≪≫
    (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).app ((forget₂ CommRingCat RingCat).obj A)

/-- The canonical finite constant coefficient comparison, with the ring-sheaf encoding
transported to abelian sheaves by the canonical constant/forgetful comparison.
Source: blueprint pullback clause 1, the constant-sheaf identifications
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def sfbFiniteCoefficientPullbackIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (f)^*[Ab.{u + 1}].obj
        ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (integralCoefficientSheaf l E Y n)) ≅
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E X n) :=
  (f)^*[Ab.{u + 1}].mapIso
    (sfbConstantRingAbIso Y
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    (constantSheafCompUpperStarIso Ab.{u + 1} f).app
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    (sfbConstantRingAbIso X
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).symm

/-- Maps from pulled-back continuous integer coefficients to one finite constant quotient
commute with base change when their adjunction mates give the same finite labeling.

Source: blueprint main-20261015, coefficient pullback proof, second paragraph;
Steps 1--2 of `det-prop-sfb-qlbar-colimit-x-pullback`.
(blueprint: lem-sfb-finite-reduction-pullback)

Proof in words. Inverse image of the sheaf represented by V is represented by its
base change: adjunction identifies maps out of that inverse image with evaluation at
the base change of V, and Yoneda gives the claimed identification, naturally in V.
Apply this to the relative test objects Y[S]. Associativity of fibre products gives
Y[S] times_Y X = X[S], naturally in S and in maps of profinite sets. For finite labels,
the representation by the coproduct of copies of the base agrees with the canonical
constant-sheaf identification: both send a constant label to its summand inclusion;
naturality in labels and sheafification give equality. The composition comparison
upperStarFromPointComp is the mate of restriction along the same fibre-product
associativity isomorphism. Consequently it sends the unit section indexed by g to
the unit section indexed by g on X[S]. The two assumed mate formulas therefore send
that section to the same map X[g followed by q]. Injectivity of the finite-label
representation gives equality of these sections. The point adjunction identifies maps
out of its left adjoint with their mates; extensionality on every S and every continuous
g (the sections of the condensed integer sheaf) proves the displayed map equality.
The argument includes the empty test object and the empty base scheme. -/
theorem sfb_finite_reduction_pullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (aX : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (aY : sfbFiniteConstantSets Y ≅ sfbFiniteRepresentables Y)
    (q : sfbIntegralProfinite l E ⟶
      FintypeCat.toProfinite.obj (sfbIntegralFiniteLevel l E n))
    (rX : (coefficientRing X (sfbCondensedIntegers l E)).X ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E X n))
    (rY : (coefficientRing Y (sfbCondensedIntegers l E)).X ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E Y n))
    (hX : ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E),
      (sfbIntegralFiniteRepresentation l E X aX n).hom.app
          (op ((profiniteToProEtOf X).obj S))
        (rX.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) (ULift.up g.hom.hom))) =
        ULift.up ((profiniteToProEtOf X).map (g ≫ q)))
    (hY : ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E),
      (sfbIntegralFiniteRepresentation l E Y aY n).hom.app
          (op ((profiniteToProEtOf Y).obj S))
        (rY.hom.app (op ((profiniteToProEtOf Y).obj S))
          (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) (ULift.up g.hom.hom))) =
        ULift.up ((profiniteToProEtOf Y).map (g ≫ q))) :
    (f)^*[Ab.{u + 1}].map rY ≫ (sfbFiniteCoefficientPullbackIso l E f n).hom =
      ((upperStarFromPointComp f).app (sfbCondensedIntegers l E).X).hom ≫ rX := by
  sorry

end AlgebraicGeometry.ProEtale
