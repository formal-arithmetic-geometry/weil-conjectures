/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.FixProjectionCompactificationComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Mixed-support cup product at the four coefficient stages

Source: current blueprint main-20261015, sec-six-functors,
sk-thm-sf-identification/def-sf-cup (blueprint: def-sf-cup).

The map is projection with second input `Ra_* L`, followed by compact-support
image of tensor with the pullback/direct-image counit. At finite coefficients
we use the datum's prescribed fixed-scalar realization of its canonical operations.
The other stages use the completed, rationalized, and common-stage operations
of the datum itself. No coherence or coefficient-comparison theorem is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

section Fixed

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [ProEtale.UpperStarPreservesFlat A]
/-- The morphism type of the fixed-coefficient cup product. Naming this exact Hom
keeps specialization at a quotient coefficient ring from expanding the derived-category
model during kernel checking.
Source: current blueprint def-sf-cup, displayed source and target (blueprint: def-sf-cup). -/
def sixFunctorFixedCupHom {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (K L : DerivedCategory (Sheaf (ProEt.topology X) A)) :
    Type (u + 1) :=
   ((ProEtale.derivedTensor A Y).obj
      ((ProEtale.rightDerivedLowerShriekOfCompactification A c).obj K)).obj
      (((ProEtale.lowerStar A a).rightDerivedFunctor).obj L) ⟶
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).obj
      (((ProEtale.derivedTensor A X).obj K).obj L)

/-- The fixed-ring presentation of the cup composite, using exactly the recorded
projection transformation and the derived pullback/direct-image counit.
Keeping the coefficient category abstract avoids reducing its monoidal instance
while elaborating the composition.
Source: current blueprint def-sf-cup, displayed composite (blueprint: def-sf-cup). -/
def sixFunctorFixedMixedSupportCupProduct {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a)
    (K L : DerivedCategory (Sheaf (ProEt.topology X) A)) :
    sixFunctorFixedCupHom A c K L :=
  ((ProEtale.projectionMapOfCompactification A c).app K).app
      (((ProEtale.lowerStar A a).rightDerivedFunctor).obj L) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).map
      (((ProEtale.derivedTensor A X).obj K).map
        ((ProEtale.derivedUpperStarLowerStarAdjunction A a).counit.app L))

end Fixed

/-- Specialization of the fixed-ring composite through the canonical intrinsic
coefficient realization. The ring stays abstract while its realization is applied.
Source: current blueprint def-sf-cup, finite stage (blueprint: def-sf-cup). -/
def sixFunctorFiniteRingCup (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (K L : proEtaleDerivedCategory X R) :=
  sixFunctorFixedMixedSupportCupProduct (ModuleCat.{u + 1} (ULift.{u + 1} R))
    (X := X) (Y := Y) (a := a) c
    ((sfIntrinsicDerivedEquivalence X R).inverse.obj K)
    ((sfIntrinsicDerivedEquivalence X R).inverse.obj L)

/-- The cup composite in the supplied operation coordinates. Its projection is the
recorded construction, not an arbitrary morphism or a chosen isomorphism.
Source: current blueprint def-sf-cup, displayed composite (blueprint: def-sf-cup). -/
def sixFunctorStageMixedSupportCupProduct {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q)
    (K L : B Q.X) :
    ((T Q.Y).obj ((S.support Q.f Q.compactification).obj K)).obj
        ((S.direct Q.f).obj L) ⟶
      (S.support Q.f Q.compactification).obj (((T Q.X).obj K).obj L) :=
  A.projectionComponent K ((S.direct Q.f).obj L) ≫
    (S.support Q.f Q.compactification).map
      (((T Q.X).obj K).map ((S.pullDirectAdjunction Q.f).counit.app L))


namespace SixFunctorDatum

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Finite-coefficient cup product, in the canonical fixed-ring realization prescribed
by the datum. The inputs are exactly finite-Tor bounded constructible objects, and
all three functors are the normalized finite operations. Projection is evaluated at
`(K, Ra_* L)`, and the second arrow is `Ra_!(1_K ⊗ ε_L)`.
Source: current blueprint def-sf-cup, finite stage (blueprint: def-sf-cup). -/
def finiteMixedSupportCupProduct (_S : SixFunctorDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :=
  @sixFunctorFiniteRingCup (Padic.coefficientExtensionRing C.l E n) _
    (Padic.finite_coefficientExtensionRing C.l E n hn)
    X.obj.left (sixFunctorPoint D).obj.left (sixFunctorStructure X).hom.left c K.obj L.obj


/-- Integral cup product formed in the datum's completed integral category.
The two inputs have the recorded integral finite-Tor property. Projection and
counit are those of the integral stage; no levelwise map is substituted.
Source: current blueprint def-sf-cup, integral stage (blueprint: def-sf-cup). -/
def integralMixedSupportCupProduct (S : SixFunctorDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory) :=
  sixFunctorStageMixedSupportCupProduct
    (B := fun Y ↦ sfIntegralConstructibleCategory C.l E Y.obj.left)
    (S := S.higher.integral) (T := S.higher.integralTensor)
    (S.higher.integralExchange
      (FixProjectionCompactification.identitySquare (sixFunctorStructure X) c)) K.obj L.obj

/-- Rational cup product using the datum's rationalized tensor, projection and counit.
At field coefficients finite Tor is the entire bounded constructible category.
Source: current blueprint def-sf-cup, rational stage (blueprint: def-sf-cup). -/
def rationalMixedSupportCupProduct (S : SixFunctorDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : sfRationalConstructibleCategory C.l E X.obj.left) :=
  sixFunctorStageMixedSupportCupProduct
    (B := fun Y ↦ sfRationalConstructibleCategory C.l E Y.obj.left)
    (S := S.higher.rational) (T := S.higher.rationalTensor)
    (S.higher.rationalExchange
      (FixProjectionCompactification.identitySquare (sixFunctorStructure X) c)) K L

/-- Algebraically closed coefficient cup product in the datum's common-stage category.
Its own operations include the recorded common-finite-field realization; the
composite introduces no new representative choices or levelwise construction.
Source: current blueprint def-sf-cup, algebraically closed stage (blueprint: def-sf-cup). -/
def commonStageMixedSupportCupProduct (S : SixFunctorDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) :=
  sixFunctorStageMixedSupportCupProduct
    (B := fun Y ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left)
    (S := S.closure.commonStage) (T := S.closure.commonStageTensor)
    (S.closure.commonStageExchange
      (FixProjectionCompactification.identitySquare (sixFunctorStructure X) c)) K L

end SixFunctorDatum
end WeilConjectures
