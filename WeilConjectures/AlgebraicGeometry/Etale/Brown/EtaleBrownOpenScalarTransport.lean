/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenScalarTransportExistence
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenScalarTransportSquare

/-! # Open scalar mate in normalized realizations

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

/-- The local open scalar square for the specified adjunction mates.
Source: Zheng, Construction 5.14 and Lemma 5.16; Stacks 07A4 and 0GL6. -/
theorem etaleBrownOpenScalarTransport
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
        (.mk _ _ _ _ (jo n).inv)) = (ro n).inverse.inv)
    {m n : ℕ} (h : m ≤ n)
    : ∃ op : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived,
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ op.hom)) = (S.openDerived.derivedTensor h).inv ∧
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
        ((RX.derived n).obj P) := by
  obtain ⟨op, hop⟩ := etaleBrownOpenScalarTransport_exists O t c S RX RZ ro jo hjo h
  refine ⟨op, hop, ?_⟩
  exact etaleBrownOpenScalarTransport_square O t c S RX RZ ro jo hjo h op hop

end AlgebraicGeometry
