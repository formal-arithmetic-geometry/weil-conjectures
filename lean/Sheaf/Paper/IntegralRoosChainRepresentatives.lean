/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosData
/-! # Integral Roos chain representatives

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks 093M, 0941, 099M and 099N.
(blueprint: lem-sfb-integral-roos-chain-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.completedModulePullback
  AlgebraicGeometry.Scheme.completedReductionModuleTowerFunctor
  AlgebraicGeometry.Scheme.OrderedExchange.reductionModule
  AlgebraicGeometry.Scheme.OrderedExchange.reductionData
  AlgebraicGeometry.Scheme.OrderedExchange.reduction
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos

/-- A finite record of comparison data, with no properties or choices in its definition.
Source: the strict cochain witnesses of det-lem-int-tensor-pullback.proof.md
(blueprint: lem-sfb-integral-roos-chain-representatives). -/
structure RoosChainWitness
    (D A E AT AU AV EP KR JR KC JC : Type*) where
  d : D
  a : A
  e : E
  αT : AT
  αU : AU
  αV : AV
  ε : EP
  κR : KR
  jR : JR
  κC : KC
  jC : JC

/-- Construct the strict cone representatives and the resolution-normalized Roos comparisons.

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks 0941 and 099N. (blueprint: lem-sfb-integral-roos-chain-representatives).

Proof: apply augmentedQuotientTowers to obtain the ordinary scalar comparison d and
balanced tower comparison a. Take e to be theta, namely d at each finite quotient
followed by inverse beta. Apply the compatible quotient augmentations to roosAugment;
the coordinates are (0,b). The scalar Roos comparison is the product comparison on
each cone summand, followed by Roos(e). Its coordinate formula is IsENormalized.
The augmented scalar Roos identity gives the strict augmentation equation. Over each
coefficient ring use the universal total-right-derived-limit comparison; its ordinary
limit inclusion has coordinates (0,z). This gives kappa and j with IsUnitNormalized.
All these assertions are on arbitrary cochain complexes, including the zero complex
and torsion terms; no K-flatness of finite quotients is asserted. -/
theorem integralRoosChainRepresentatives
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    ∃ w : RoosChainWitness
      (pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
      (T l E g ≅ U l E g) (T l E g ⋙ towerRes l E X ≅ V l E g)
      (alphaTType l E g) (alphaUType l E g) (alphaVType l E g) (EType l E g)
      (kappaType X (R l E X)) (inclusionType X (R l E X))
      (kappaType X (C l E X)) (inclusionType X (C l E X)),
      PulledReduction.IsOrdinaryNormalized (datum l E) g w.d.inv ∧
      IsLambdaNormalized l E g w.a ∧
      (∀ (M : ModR l E Y) (n : ℕ), (w.e.hom.app M).app (op n) =
        w.d.hom.app (((redR l E Y).obj M).obj (op n)) ≫
          (pullC l E g).map
            (((OrderedExchange.ordinaryRho (datum l E) Y).inv.app M).app (op n))) ∧
      IsAugmentationNormalized l E g w.αT w.αU w.αV ∧
      IsENormalized l E g w.e w.ε ∧
      (∀ P : complexesR l E Y,
        (cxRes l E X).map (w.αT P) ≫ (w.ε P).hom =
          (dComplex l E g w.d).hom.app P ≫ w.αV P) ∧
      IsUnitNormalized X (R l E X) w.κR w.jR ∧ IsUnitNormalized X (C l E X) w.κC w.jC := by sorry

end WeilConjectures.IntegralPullbackStrictRoos
