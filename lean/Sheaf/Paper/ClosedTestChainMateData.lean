/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClosedTestKInjectiveSectionModels
public import Sheaf.Paper.ClosedTestDerivedExchangeModel
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous


/-! # Ordinary and chain constructions for closed-test mates

Source: Stacks Project, proetale.tex, Tag 09BL; derived.tex, Tag 09T5;
sites-cohomology.tex, Tags 08FI, 0D6E and 0D6F; the unit--counit calculation
(blueprint: lem-sfb-closed-test-chain-mate-restriction).

(blueprint: def-sfb-closed-test-chain-mate-data).

The existing derived exchange, restriction and section-composition maps are reused.
The new maps below are their ordinary chain representatives on the specified tests.
-/

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

/-- Cache additivity of evaluation of the same underlying internal module.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
instance (priority := 2500) evaluationAdditive {X : Scheme.{u}} (V : X.ProEt) :
    (evaluation Λ V).Additive := inferInstance


/-- The ordinary canonical pullback comparison, using the specified module compositors.
Source: Stacks 09BL, 04J0 (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def ordinarySquare {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    CondensedRing.upperStar Λ s ⋙ CondensedRing.upperStar Λ fZ ≅
      CondensedRing.upperStar Λ f ⋙ CondensedRing.upperStar Λ h :=
  (CondensedRing.upperStarComp Λ fZ s).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) w.w.symm) ≪≫
      CondensedRing.upperStarComp Λ h f

/-- Ex-zero is the specified adjunction square mate, before passing to complexes.
Source: Stacks 09BL, unit--counit calculation
(blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def ordinaryExchange {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    CondensedRing.lowerStar Λ f ⋙ CondensedRing.upperStar Λ s ⟶
      CondensedRing.upperStar Λ h ⋙ CondensedRing.lowerStar Λ fZ :=
  Adjunction.squareExchange (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ fZ)
    (CondensedRing.upperStar Λ s) (CondensedRing.upperStar Λ h) (ordinarySquare Λ w)

/-- The actual arrow T0 to h-inverse-image of T in the small site of XZ.
Source: Stacks 09BK, 09BL (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def testSectionArrow (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt) :
    testFibre fZ (closedTest A a V) ⟶ testFibre h (testFibre f (liftedTest A a V)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (testArrow A a w V) (testFibre fZ (closedTest A a V)).hom
      (pullback.lift_snd _ _ _)) (pullback.lift_snd _ _ _)

/-- The actual inverse-image unit evaluated on T and restricted to T0.
Its localized form is the unit for a, with testPullbackComposition as coefficient comparison.
Source: Stacks 09BL, 03D3 (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def testSectionUnit (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt) :
    evaluation Λ (testFibre f (liftedTest A a V)) ⟶
      CondensedRing.upperStar Λ h ⋙ evaluation Λ (testFibre fZ (closedTest A a V)) :=
  Functor.whiskerRight (CondensedRing.upperStarLowerStarAdjunction Λ h).unit
      (evaluation Λ (testFibre f (liftedTest A a V))) ≫
    (Functor.associator (CondensedRing.upperStar Λ h) (CondensedRing.lowerStar Λ h)
      (evaluation Λ (testFibre f (liftedTest A a V)))).hom ≫
    Functor.whiskerLeft (CondensedRing.upperStar Λ h)
      ((pushEvaluation Λ h (testFibre f (liftedTest A a V))).hom ≫
        evaluationMap Λ (testSectionArrow A a w V))

/-- The canonical final-object section identity, retaining its explicit normalization.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def terminalSections (X : Scheme.{u}) :
    condensedModuleSections Λ X ≅ evaluation Λ (Scheme.ProEt.mk (𝟙 X)) :=
  Iso.refl _

/-- The existing section-localization comparison in the global-sections encoding.
The only change is the specified final-object section identity terminalSections.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def globalLocalizationModel {X : Scheme.{u}} (V : X.ProEt)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (e : DerivedCategory.Q.obj L ≅ K) :
    DerivedCategory.Q.obj ((complexes (evaluation Λ V)).obj L) ⟶
      (ClosedTestDerivedExchangeModel.sectionsOver Λ V.hom).obj K :=
  localizationModel Λ V K L e ≫
    (Functor.rightDerivedFunctorNatIso (terminalSections Λ V.left)).inv.app
      ((CondensedRing.upperStar Λ V.hom).mapDerivedCategory.obj K)

/-- The literal direct-image pasting comparison, with no choice of adjunction.
Source: Stacks 0D6E, 04J0 (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def directSquare {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    CondensedRing.lowerStar Λ h ⋙ CondensedRing.lowerStar Λ f ≅
      CondensedRing.lowerStar Λ fZ ⋙ CondensedRing.lowerStar Λ s :=
  CondensedRing.lowerStarComp Λ h f ≪≫
    eqToIso (congrArg (CondensedRing.lowerStar Λ) w.w) ≪≫
      (CondensedRing.lowerStarComp Λ fZ s).symm

/-- The right-derived pasting comparison, with its K-injective composition units.
Source: Stacks 0D6E (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def derivedDirectSquare {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    (CondensedRing.lowerStar Λ h).rightDerivedFunctor ⋙
        (CondensedRing.lowerStar Λ f).rightDerivedFunctor ≅
      (CondensedRing.lowerStar Λ fZ).rightDerivedFunctor ⋙
        (CondensedRing.lowerStar Λ s).rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (directSquare Λ w) ≪≫
      Functor.rightDerivedFunctorCompIso _ _
/-- Evaluate Ex-zero after the actual closed unit, using both literal direct-image formulas.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def evaluatedExchange
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt) :
    evaluation Λ (testFibre f (liftedTest A a V)) ⟶
      CondensedRing.upperStar Λ h ⋙ evaluation Λ (testFibre fZ (closedTest A a V)) :=
  (pushEvaluation Λ f (liftedTest A a V)).inv ≫
    Functor.whiskerLeft (CondensedRing.lowerStar Λ f) (closedUnit Λ A a V) ≫
        (Functor.associator (CondensedRing.lowerStar Λ f)
          (CondensedRing.upperStar Λ (closedMap A a))
          (evaluation Λ (closedTest A a V))).inv ≫
        Functor.whiskerRight (ordinaryExchange Λ w.toCommSq)
          (evaluation Λ (closedTest A a V)) ≫
        (Functor.associator (CondensedRing.upperStar Λ h)
          (CondensedRing.lowerStar Λ fZ) (evaluation Λ (closedTest A a V))).hom ≫
        Functor.whiskerLeft (CondensedRing.upperStar Λ h)
          (pushEvaluation Λ fZ (closedTest A a V)).hom

/-- The specified ordinary mate followed by the target K-injective resolution.
Source: Stacks 09T5, 09BL (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def chainMate {X U XZ Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Z} (w : CommSq h fZ f s)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (J : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1})
      (condensedRingObj Λ XZ)) ℤ)
    (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J) :
    (complexes (CondensedRing.upperStar Λ s)).obj
        ((complexes (CondensedRing.lowerStar Λ f)).obj L) ⟶
      (complexes (CondensedRing.lowerStar Λ fZ)).obj J :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (CondensedRing.lowerStar Λ f ⋙ CondensedRing.upperStar Λ s)) (.up ℤ)).hom.app L ≫
  (NatTrans.mapHomologicalComplex (ordinaryExchange Λ w) (.up ℤ)).app L ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (CondensedRing.upperStar Λ h ⋙ CondensedRing.lowerStar Λ fZ))
      (.up ℤ)).inv.app L ≫
    (complexes (CondensedRing.lowerStar Λ fZ)).map j


/-- The evaluated restriction chain map, using the actual unit and the supplied j.
Source: Stacks 09BL, 0D6F (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def sectionChain (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (J : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1})
      (condensedRingObj Λ XZ)) ℤ)
    (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J) :
    (complexes (evaluation Λ (testFibre f (liftedTest A a V)))).obj L ⟶
      (complexes (evaluation Λ (testFibre fZ (closedTest A a V)))).obj J :=
  (NatTrans.mapHomologicalComplex (testSectionUnit Λ A a w V) (.up ℤ)).app L ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (CondensedRing.upperStar Λ h ⋙
        evaluation Λ (testFibre fZ (closedTest A a V)))) (.up ℤ)).inv.app L ≫
    (complexes (evaluation Λ (testFibre fZ (closedTest A a V)))).map j

/-- Degreewise evaluation of the specified mate followed by j, with composition assembled
before passing to complexes. This retains the ordinary units, counits and literal sections.
Source: Stacks 09BL, 0D6F (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def evaluatedChainMate (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (J : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1})
      (condensedRingObj Λ XZ)) ℤ)
    (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J) :
    (complexes (evaluation Λ (testFibre f (liftedTest A a V)))).obj L ⟶
      (complexes (evaluation Λ (testFibre fZ (closedTest A a V)))).obj J :=
  (NatTrans.mapHomologicalComplex (evaluatedExchange Λ A a f h fZ w V) (.up ℤ)).app L ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (CondensedRing.upperStar Λ h ⋙
        evaluation Λ (testFibre fZ (closedTest A a V)))) (.up ℤ)).inv.app L ≫
    (complexes (evaluation Λ (testFibre fZ (closedTest A a V)))).map j

/-- The literal direct-image section formula on complexes, with explicit composition factors.
Source: Stacks 09BL, 0D6F (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def pushEvaluationChain {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEt)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) :
    (complexes (evaluation Λ V)).obj ((complexes (CondensedRing.lowerStar Λ f)).obj L) ≅
      (complexes (evaluation Λ (testFibre f V))).obj L :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (CondensedRing.lowerStar Λ f ⋙ evaluation Λ V)) (.up ℤ)).app L ≪≫
      (NatIso.mapHomologicalComplex (pushEvaluation Λ f V) (.up ℤ)).app L

/-- Unit/counit compatibility of the specified ordinary and derived pasting maps.
Both equalities use the actual adjunctions, rather than choosing structures on isomorphic functors.
Source: Stacks 09T5, 0D6E (blueprint: lem-sfb-closed-test-chain-mate-restriction). -/
def pastingAdjunctionCompatible {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) : Prop :=
  HEq (directSquare Λ w)
    (conjugateIsoEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ h))
      ((CondensedRing.upperStarLowerStarAdjunction Λ s).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ fZ))
      (ordinarySquare Λ w)) ∧
  HEq (derivedDirectSquare Λ w)
    (conjugateIsoEquiv
      ((ClosedTestDerivedExchangeModel.adj Λ f).comp
        (ClosedTestDerivedExchangeModel.adj Λ h))
      ((ClosedTestDerivedExchangeModel.adj Λ s).comp
        (ClosedTestDerivedExchangeModel.adj Λ fZ))
      (ClosedTestDerivedExchangeModel.square Λ w))

end AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction
