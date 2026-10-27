/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import all Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate
import Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange
import Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import all Sheaf.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1EvaluationRecipeBaseChange

/-! # The two ordinary projective-line components commute with arbitrary base change

Source: main-20261015, thm-amb-p1-decomposition.proof.md, Cartier class and base change
(blueprint: lem-asd-ordinary-finite-p1-kummer-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local irreducible] singleFunctorPullbackMap
  upperStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem adjunct_square_core
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {P : C} {P' : E} {K : D} {K' : F}
    (z : L.obj P ⟶ K) (z' : L'.obj P' ⟶ K') (b : G.obj P ⟶ P')
    (d : H.obj K ⟶ K')
    (hz : θ.natTrans.app P ≫ H.map z ≫ d = L'.map b ≫ z') :
    G.map (adj.homEquiv _ _ z) ≫ (mateEquiv adj adj' θ).natTrans.app K ≫ R'.map d =
      b ≫ adj'.homEquiv _ _ z' := by
  rw [reassoc_of% adjunct_mate adj adj' G H θ z]
  rw [← adj'.homEquiv_naturality_right, ← adj'.homEquiv_naturality_left]
  apply congrArg (adj'.homEquiv _ _)
  simpa only [Category.assoc] using hz

private theorem native_general_adjunct_square (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    {P : DerivedCategoryModule A Y} {P' : DerivedCategoryModule A Y'}
    {K : DerivedCategoryModule A X} {K' : DerivedCategoryModule A X'}
    (z : (ordinaryFinitePullback A q).obj P ⟶ K)
    (z' : (ordinaryFinitePullback A q').obj P' ⟶ K')
    (b : (ordinaryFinitePullback A f).obj P ⟶ P')
    (d : (ordinaryFinitePullback A g).obj K ⟶ K')
    (hz : (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app P ≫
      (ordinaryFinitePullback A g).map z ≫ d = (ordinaryFinitePullback A q').map b ≫ z') :
    (ordinaryFinitePullback A f).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q).homEquiv _ _ z) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K ≫
        (ordinaryFinitePushforward A q').map d =
      b ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q').homEquiv _ _ z' := by
  dsimp only [derivedBaseChangeMap, derivedBaseChangeSquare, ordinaryFinitePushforward,
    ordinaryFinitePullback]
  exact adjunct_square_core
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q')
    (ordinaryFinitePullback A f) (ordinaryFinitePullback A g)
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom)
    z z' b d hz

/-- The actual scalar Kummer class pulls back to the actual scalar Kummer class,
and its evaluation adjunct, as well as the constant unit, commutes with exchange.
This is a statement about the two components, with no splitting or invertibility
assertion and no Noetherian assumption.
Source: main-20261015, thm-amb-p1-decomposition.proof.md, arbitrary-base paragraph
(blueprint: lem-asd-ordinary-finite-p1-kummer-base-change).

Proof: let D be the hyperplane x_0=0. On x_1 nonzero its ideal is (s), where
s=x_0/x_1, and on x_0 nonzero its ideal is the unit ideal. Multiplication by s in
B[s] is injective for every ring B by comparison of coefficients, including after
arbitrary base change. Thus D and its pullback D' are effective Cartier divisors.
The dual ideal frames e_0=1 and e_1=s^{-1} satisfy e_0=t^{-1}e_1, so their line
bundles are exactly the specified O(1). Apply ordinary_supported_kummer to D and
the Cartier pullback D'. Its boundary determines the classes uniquely. Its unit
and Chern equation identifies the first class with c by the assumed specification;
the pulled-back boundary supplies c' with the displayed specification. The supported
pullback square, followed by the mate unit identity for the divisor square, gives
the Chern-class pullback equation, with the canonical normalized twist comparison.
For the projective-line square the mate unit identity gives the constant component
equation. For the second component the mate counit identity identifies its adjunct
with pullback of the adjunct defining h. Inverse image preserves tensor and the
unit, signed shifts and evaluation; the evaluation equation is the normalized
negative-twist equation in etaleFiniteTwistPullback, transported through the canonical
degree-zero and shift comparisons. Substitute the Chern-class pullback equation.
The result is the adjunct defining h' after the negative-twist pullback comparison.
Injectivity of the adjunction correspondence proves the second component equation.
No proper-exchange invertibility is used, and no flatness of A over Z/N is required.
This proof also applies to zero coefficients, N=1, empty bases and nonreduced bases. -/
theorem ordinaryFiniteP1_components_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) c) :
    ∃ c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S'
        ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
          hS'.map (ProjectiveLine S' ↘ S').appTop.hom) c' ∧
      ((ordinaryFinitePullback A g).map (p1DecompositionUnit A S) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
        (ordinaryFiniteUnitPullback A g).hom ≫ p1DecompositionUnit A S') ∧
      ((ordinaryFinitePullback A g).map (p1DecompositionChernAdjoint A N hN hA S hS c) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
        (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom ≫
          p1DecompositionChernAdjoint A N hN hA S' hS' c') := by
  let hP' : IsUnit (N : Γ(ProjectiveLine S', ⊤)) :=
    (map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
      hS'.map (ProjectiveLine S' ↘ S').appTop.hom
  obtain ⟨c', hc'⟩ := (ordinaryFiniteClass_bijective_arbitraryBase A (ProjectiveLine S')
    (Scheme.finiteEtaleTateLine (ProjectiveLine S') N A hA) 2).2
      (ordinaryFiniteP1KummerClass A N hA S' hP')
  have hc'spec : ordinaryFiniteP1ChernSpec A N hA S' hP' c' := hc'
  refine ⟨c', hc'spec, ?_, ?_⟩
  · unfold p1DecompositionUnit
    rw [line_projective_exchange]
    have h := native_adjunct_square A
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq
      (𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)))
      (𝟙 (ordinaryFiniteUnit A (ProjectiveLine S')))
      (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom
      (by simp)
    simpa only [Category.comp_id] using h
  · have hcmap := ordinaryFiniteP1_chern_map_baseChange A N hN hA
      (positive_transport A N hN hA) g hS hS' c c' hc hc'spec
    have hz := ordinaryFiniteP1_evaluationRecipe_baseChange A N hN hA
      (positive_transport A N hN hA)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq hS hS'
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) hP' c c' hcmap
    unfold p1DecompositionChernAdjoint
    rw [p1DecompositionTensorAdjoint, p1DecompositionTensorAdjoint, line_projective_exchange]
    exact native_general_adjunct_square A
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq _ _
      (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom
      (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom hz

end AlgebraicGeometry.Etale
