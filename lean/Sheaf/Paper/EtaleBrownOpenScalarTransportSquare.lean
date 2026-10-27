/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex D7
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization

/-! # Open scalar transport decomposition

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The normalized open scalar mate satisfies the transport square.
Source: Zheng, Constructions 5.14--5.15 and Lemma 5.16; Stacks 03S6, 07A4.
(blueprint: lem-pur-etale-brown-open-scalar-transport-square).

The proof transposes both paths through the open adjunction, applies the
normalization of the supplied comparison `jo` and of the supplied mate `op`,
and uses the scalar/open exchange identity on cochain representatives. -/
theorem etaleBrownOpenScalarTransport_square
    (O : Type (u + 1)) [CommRing O] (t : O)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : StrictEtaleCompactSupport O t c)
    (RX : StrictEtaleBrownRealization O t X S.PX)
    (RZ : StrictEtaleBrownRealization O t c.Z S.PZ)
    (ro : ∀ n, StrictEtaleBrownImageRealization O t c.i n
      S.openImage (S.openDerived.level n) RX RZ)
    (jo : ∀ n, S.levelDerivedOpen n ⋙ RZ.derived n ≅
      RX.derived n ⋙ (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory)
    (hjo : ∀ n,
      (mateEquiv (S.levelDerivedOpenAdjunction n)
        (((Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
        (.mk _ _ _ _ (jo n).inv)).natTrans = (ro n).inverse.inv)
    {m n : ℕ} (h : m ≤ n) (op : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
    (hop :
      (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
        (.mk _ _ _ _ op.hom)).natTrans = (S.openDerived.derivedTensor h).inv) :
    ∀ P : DerivedCategory (strictEtaleLevel X O t n),
    (RZ.derived m).map (op.inv.app P) ≫
      (jo m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c.i).mapDerivedCategory.map
        ((RX.scalar h).hom.app P) =
    (RZ.scalar h).hom.app ((S.levelDerivedOpen n).obj P) ≫
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) c.Z).map
        ((jo n).hom.app P) ≫
      (Etale.ExceptionalCoefficients.openIso (strictEtaleBrownRingMap O t h) c.i).hom.app
        ((RX.derived n).obj P) := by sorry

end AlgebraicGeometry
