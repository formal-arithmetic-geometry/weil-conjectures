/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization
public import Sheaf.Paper.FiniteFieldFiber

/-! # Normalized finite-level geometric comparisons

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16,
printed pp. 21 and 34--35; Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- Normalized realizations and coefficient projection, without singleton extension.
Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16,
printed pp. 21 and 34--35; Stacks 03CY, 06YY and 07A4
(blueprint: lem-pur-etale-brown-level-comparisons).

Proof: restriction along the constant-ring sheafification unit is an additive
equivalence, retaining sections and maps. Localize it exactly to obtain the three
level realizations. The identity on sections gives ordinary scalar restriction;
localization fixes its derived comparison, and the scalar-adjunction mate fixes scalar
extension. Identify ordinary geometric direct images on each section. Uniqueness of
their universal right derived functors, with the specified units, gives the right-image
comparison; its adjunction mate gives inverse image. The open extension comparison is
the mate against the two open extension/restriction adjunctions. Compose it with the
proper right-image comparison to define levelComparison, by associativity.
Take the mates of the recorded derivedTensor maps for the proper and open factors.
After the normalized realizations, the proper mate is the published proper coefficient
projection and the open mate is the scalar-balancing comparison. The finite torsion
coefficient projection theorem makes the former invertible; the latter is already an
isomorphism. Their composite defines projection, by associativity. Applying the
scalar transpose equations and composing the two geometric counits identifies its
inverse with compactScalarMap, which is projection_recorded_q. This uses neither
singleton extensions nor any Brown adjoint. Identity transitions and the zero quotient
ring are included: their normalized units and the same mate calculation apply. -/
theorem etaleBrownLevelComparisons
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (O : Type (u + 1)) [CommRing O] (t : O)
    (hfinite : ∀ n : ℕ, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n : ℕ, ∃ a : ℕ, (l ^ a : strictEtaleBrownRing O t n) = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (S : StrictEtaleCompactSupport O t c) :
    ∃ (realizationX : StrictEtaleBrownRealization O t X S.PX)
      (realizationZ : StrictEtaleBrownRealization O t c.Z S.PZ)
      (realizationY : StrictEtaleBrownRealization O t Y S.PY)
      (properRealization : ∀ n, StrictEtaleBrownImageRealization O t c.g n
    S.properImage (S.properDerived.level n) realizationZ realizationY)
      (openRealization : ∀ n, StrictEtaleBrownImageRealization O t c.i n
    S.openImage (S.openDerived.level n) realizationX realizationZ)
      (openComparison : ∀ n, S.levelDerivedOpen n ⋙ realizationZ.derived n ≅
    realizationX.derived n ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory)
      (openProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
      (properProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level m).direct ≅
      (S.properDerived.level n).direct ⋙ (S.PY.scalar h).derived),
      (∀ n,
    (mateEquiv (S.levelDerivedOpenAdjunction n)
      (((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
      (.mk _ _ _ _ (openComparison n).inv)).natTrans = (openRealization n).inverse.inv) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ (openProjection h).hom)).natTrans = (S.openDerived.derivedTensor h).inv) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
    (properProjection h).inv =
      (mateEquiv (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans) ∧
      (let levelComparison (n : ℕ) :
          S.levelFunctor n ⋙ realizationY.derived n ≅
            realizationX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c :=
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (properRealization n).right ≪≫
          (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (openComparison n) _ ≪≫
          Functor.associator _ _ _
      let projection {m n : ℕ} (h : m ≤ n) :
          (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
            S.levelFunctor n ⋙ (S.PY.scalar h).derived :=
        (Functor.associator _ _ _).symm ≪≫
          isoWhiskerRight (openProjection h) _ ≪≫ Functor.associator _ _ _ ≪≫
          isoWhiskerLeft _ (properProjection h) ≪≫ (Functor.associator _ _ _).symm
      ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
        ((levelComparison n).inv.app P) ≫
      (realizationY.scalar h).inv.app ((S.levelFunctor n).obj P) ≫
      (realizationY.derived m).map ((projection h).inv.app P) ≫
      (levelComparison m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c).map
          ((realizationX.scalar h).hom.app P) =
    (Etale.compactScalarMap (strictEtaleBrownRingMap O t h) c).app
      ((realizationX.derived n).obj P)) := by sorry

end AlgebraicGeometry
