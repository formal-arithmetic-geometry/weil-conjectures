/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClosedTestChainMateData

/-! # Localization of the closed-test section-unit chain
Source: Stacks sites-cohomology.tex Tags 08FI, 0D6E and 0D6F; derived.tex Tag 09T5.
(blueprint: lem-sfb-closed-test-chain-unit-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction
open ClosedTestKInjectiveSectionModels
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual section-unit chain represents the normalized localized derived restriction.
Proof: Restrict L to T and J to T0, and identify their localized module categories
with the section-ring models. Exact localization preserves K-injectivity. Pullback
composition turns the restriction of j into a resolution of a-star of restricted L.
Apply the normalized derived Hom bijection for a-star adjoint to a-star pushforward:
the ordinary adjunct of that resolution is its pushforward after the actual unit.
Thus its localized class is the derived unit. The pushforward of restricted J is
K-injective since its left adjoint is exact. Compute derived sections on this
representative. The direct-image composition comparison is normalized by the literal
degreewise identity Gamma(T,a_*J)=Gamma(T0,J). The terminal-object
section comparisons in the displayed formula retain this normalization. After
forgetting the coefficient action the resulting arrow is exactly the displayed
section unit followed by j. All comparisons are natural in e; cancel Q(j) using its
quasi-isomorphism, without assuming h-star L K-injective.
Source: Stacks sites-cohomology.tex Tags 08FI, 0D6E and 0D6F; derived.tex Tag 09T5.
(blueprint: lem-sfb-closed-test-chain-unit-normalization). -/
theorem closed_test_chain_unit_normalization
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [L.IsKInjective] (e : DerivedCategory.Q.obj L ≅ K.obj)
    (J : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1}) (condensedRingObj Λ XZ)) ℤ)
    [J.IsKInjective] (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J)
    [QuasiIso j] :
    HEq (DerivedCategory.Q.map (sectionChain Λ A a w V L J j) ≫
        globalLocalizationModel Λ (testFibre fZ (closedTest A a V))
          ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
          J (pullRepresentative Λ h K.obj L e J j))
      (globalLocalizationModel Λ (testFibre f (liftedTest A a V)) K.obj L e ≫
        (ClosedTestDerivedExchangeModel.restriction Λ (testArrow A a w V)).app
          ((CondensedRing.upperStar Λ
            (testFibre f (liftedTest A a V)).hom).mapDerivedCategory.obj K.obj) ≫
        (condensedModuleSections Λ
          (testFibre fZ (closedTest A a V)).left).rightDerivedFunctor.map
            ((derivedTestPullbackComposition Λ A a w V).inv.app K.obj)) := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction
