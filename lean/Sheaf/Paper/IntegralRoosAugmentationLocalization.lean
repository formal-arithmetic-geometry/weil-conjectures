/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosData
/-! # Integral Roos augmentation localization

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks 093M, 0941, 099M and 099N.
(blueprint: lem-sfb-integral-roos-augmentation-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos

/-- Identify the normalized strict cone augmentations after localization with
both quotient-completion units and the pulled-tower comparison.

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks 0941, 099M and 099N. (blueprint: lem-sfb-integral-roos-augmentation-localization).

Proof: the coordinate normalization fixes each augmentation uniquely as (0,b).
The universal normalized Roos comparison identifies that map with the constant-tower
unit followed by derived inverse limit of the strict augmentation. Apply the derived
reduction computation on flat K-flat representatives to U. For V first use the
specified constantTowerIso, which intertwines the quotient augmentations on tensor
generators, and then the constant reduction counit. For T exact inverse image and its
universal counit identify the same strict augmentation with completedPullbackComparison.
No input completeness is required; these are equations before inverting a completion unit. -/
theorem integralRoosAugmentationLocalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (αT : alphaTType l E g) (αU : alphaUType l E g) (αV : alphaVType l E g)
    (ε : EType l E g)
    (κR : kappaType X (R l E X)) (jR : inclusionType X (R l E X))
    (κC : kappaType X (C l E X)) (jC : inclusionType X (C l E X))
    (hd : PulledReduction.IsOrdinaryNormalized (datum l E) g d.inv)
    (ha : IsLambdaNormalized l E g a)
    (he : ∀ (M : ModR l E Y) (n : ℕ), (e.hom.app M).app (op n) =
      d.hom.app (((redR l E Y).obj M).obj (op n)) ≫
        (pullC l E g).map
          (((OrderedExchange.ordinaryRho (datum l E) Y).inv.app M).app (op n)))
    (hα : IsAugmentationNormalized l E g αT αU αV)
    (hε : IsENormalized l E g e ε)
    (hE : ∀ P : complexesR l E Y,
      (cxRes l E X).map (αT P) ≫ (ε P).hom =
        (dComplex l E g d).hom.app P ≫ αV P)
    (hκR : IsUnitNormalized X (R l E X) κR jR)
    (hκC : IsUnitNormalized X (C l E X) κC jC) :
    (∀ (P : complexesR l E Y), GoodR l E Y P →
      DerivedCategory.Q.map (αU P) ≫ κR.hom.app ((cxU l E g).obj P) =
        unitR l E X (DerivedCategory.Q.obj ((cxPullR l E g).obj P)) ≫
          (completedRlim X (R l E X)).map
            (completedReductionTowerComplexCounit X (datum l E)
              ((cxPullR l E g).obj P))) ∧
    (∀ (P : complexesR l E Y), GoodR l E Y P →
      completedOrdinaryPullbackComplexCounit g (datum l E) P ≫
          DerivedCategory.Q.map (αT P) ≫ κR.hom.app ((cxT l E g).obj P) =
        completedPullbackComparison g (datum l E) (DerivedCategory.Q.obj P) ≫
          (completedRlim X (R l E X)).map (towerCounit l E g P)) ∧
    IsConstantUnitNormalized l E g d a e αV κC := by sorry

end WeilConjectures.IntegralPullbackStrictRoos
