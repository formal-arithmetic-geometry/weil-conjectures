/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClosedTestChainMateData

/-! # K-injective representative of the derived square mate
Source: Stacks derived.tex Tags 0FND and 09T5; proetale.tex Tag 09BL.
(blueprint: lem-sfb-closed-test-chain-exchange-normalization). -/

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

/-- The ordinary chain mate followed by the supplied resolution represents derived exchange.
Proof: Apply the normalized derived adjunction Hom bijections to f and fZ. Exactness
of inverse image makes the left comparisons exact localization factors. On the
K-injective L the derived counit is the ordinary counit. The adjunct of the displayed
chain map is j composed with h-star of that counit and the pullback compositor.
Naturality moves Q(j) through the Hom bijection, and its inverse in pullRepresentative
cancels it. Transport along e and use naturality of the derived mate. The two arrows
have equal adjuncts, so injectivity of the adjunction Hom equivalence proves equality.
No contractibility or invertibility of exchange is used.
Source: Stacks derived.tex Tags 0FND and 09T5; proetale.tex Tag 09BL.
(blueprint: lem-sfb-closed-test-chain-exchange-normalization). -/
theorem closed_test_chain_exchange_normalization
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
    HEq (DerivedCategory.Q.map (chainMate Λ w.toCommSq L J j) ≫
        pushModel Λ fZ ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
          J (pullRepresentative Λ h K.obj L e J j))
      ((CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategoryFactors.inv.app
          ((complexes (CondensedRing.lowerStar Λ f)).obj L) ≫
        (CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory.map
          (pushModel Λ f K.obj L e) ≫
        (ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app K.obj) := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction
