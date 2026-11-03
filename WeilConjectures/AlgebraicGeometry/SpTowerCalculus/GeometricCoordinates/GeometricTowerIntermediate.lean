/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGeometricAssembly
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions

/-! # The intermediate word between the tower mate and its compositors

Source: Stacks 0F7J, the four displayed functors of the composition calculation.
(blueprint: def-sp-geometric-tower-intermediate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

/-- Paste two specified evaluation squares, with their associators.
Source: natural-isomorphism composition
(blueprint: def-sp-geometric-tower-intermediate). -/
def pasteEvaluations
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {F : C ⥤ D} {G : D ⥤ E} {P : C' ⥤ D'} {Q : D' ⥤ E'}
    {EC : C ⥤ C'} {ED : D ⥤ D'} {EE : E ⥤ E'}
    (a : F ⋙ ED ≅ EC ⋙ P) (b : G ⋙ EE ≅ ED ⋙ Q) :
    (F ⋙ G) ⋙ EE ≅ EC ⋙ (P ⋙ Q) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ b ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight a _ ≪≫
      Functor.associator _ _ _

/-- Transport an evaluation square through the two recorded realizations.
This is a word in the given counit and evaluation comparisons.
Source: equivalence transport
(blueprint: def-sp-geometric-tower-intermediate). -/
def realizeEvaluation
    {C D S T C' D' : Type*}
    [Category C] [Category D] [Category S] [Category T] [Category C'] [Category D']
    (e : C ≌ S) (d : D ≌ T)
    {Q : C ⥤ C'} {R : D ⥤ D'} {U : S ⥤ C'} {V : T ⥤ D'}
    (a : e.functor ⋙ U ≅ Q) (b : d.functor ⋙ V ≅ R)
    {W : S ⥤ T} {P : C' ⥤ D'} (v : W ⋙ V ≅ U ⋙ P) :
    (e.functor ⋙ W ⋙ d.inverse) ⋙ R ≅ Q ⋙ P :=
  Functor.isoWhiskerLeft (e.functor ⋙ W ⋙ d.inverse) b.symm ≪≫
    Functor.isoWhiskerLeft (e.functor ⋙ W)
      (Functor.isoWhiskerRight d.counitIso V) ≪≫
    Functor.isoWhiskerLeft e.functor v ≪≫ Functor.isoWhiskerRight a P

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The old system word after interchanging the middle proper/open pair.
It is constructed on all unbounded complexes and uses no origin witness.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
abbrev towerIntermediateSystem
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :=
  ((SpTowerShriek.openD l E b (o.openOp T.cf.i) ⋙
    SpTowerShriek.openD l E b (o.openOp T.q)) ⋙
    SpTowerShriek.push l E b (o.geometry T.p)) ⋙
    SpTowerShriek.push l E b (o.geometry T.cg.g)

/-- The same intermediate word in the supplied coefficient-tower category.
Source: Local pairs, fixed realization
(blueprint: def-sp-geometric-tower-intermediate). -/
abbrev towerIntermediate
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :=
  (realization l E b X (q.abelian X)).functor ⋙
    towerIntermediateSystem l E b o T ⋙
    (realization l E b Z (q.abelian Z)).inverse

/-- The four finite intrinsic factors, before composing either pair.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
abbrev finiteTowerIntermediateIntrinsic
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :=
  ((sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) T.cf.i ⋙
    sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) T.q) ⋙
    (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) T.p).rightDerivedFunctor) ⋙
    (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) T.cg.g).rightDerivedFunctor

/-- The intrinsic intermediate word followed by fixed module realization.
Source: finite coefficient coordinates
(blueprint: def-sp-geometric-tower-intermediate). -/
abbrev finiteTowerIntermediate
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :=
  finiteTowerIntermediateIntrinsic l E T n ⋙
    (sfIntrinsicDerivedEquivalence Z (SpTowerShriek.R l E n)).inverse

/-- Evaluation of the four individual factors is pasted before any compositor.
Source: finite proper and open evaluations
(blueprint: def-sp-geometric-tower-intermediate). -/
def towerIntermediateSystemEvaluation
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :
    towerIntermediateSystem l E b o T ⋙ SpTowerShriek.Ev l E Z n ≅
      SpTowerShriek.Ev l E X n ⋙ finiteTowerIntermediateIntrinsic l E T n :=
  pasteEvaluations
    (pasteEvaluations
      (pasteEvaluations
        (SpTowerShriek.openEvaluation l E b (o.openOp T.cf.i) n)
        (SpTowerShriek.openEvaluation l E b (o.openOp T.q) n))
      ((o.geometry T.p).pushEvaluation n))
    ((o.geometry T.cg.g).pushEvaluation n)

/-- The intermediate finite evaluation, fixed before either tower compositor.
It only pastes the four normalized individual factor evaluations.
Source: Levels, ordinary evaluation
(blueprint: def-sp-geometric-tower-intermediate). -/
def towerIntermediateEvaluation
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :
    towerIntermediate l E b o q T ⋙ fixedLevel l E b q Z n ≅
      spDerivedCoefficientEvaluation l E X (q.abelian X) n ⋙
        finiteTowerIntermediate l E T n :=
  Functor.isoWhiskerRight
    (realizeEvaluation (realization l E b X (q.abelian X))
      (realization l E b Z (q.abelian Z))
      (levelComparison l E b q X n) (levelComparison l E b q Z n)
      (towerIntermediateSystemEvaluation l E b o T n)) _

/-- Exact open coordinates in the fixed varying-ring model.
Source: ordinary adjunction comparison followed by exact localization
(blueprint: def-sp-geometric-tower-intermediate). -/
def graphSystemOpenCoordinates
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    SpTowerShriek.openD l E b (o.openOp j) ⋙
        (g.presentation X).functor.mapDerivedCategory ≅
      (g.presentation U).functor.mapDerivedCategory ⋙
        VaryingRing.J (graphRings l E) (graphTransitions l E) j :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (graphForward l E b o g _ _ (graphOpenCoordinates l E b o g j)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (semilinear_open_eq l E j))

/-- Total proper coordinates in the fixed varying-ring model.
Source: canonical right-derived comparison of the section-normalized push square
(blueprint: def-sp-geometric-tower-intermediate). -/
def graphSystemProperCoordinates
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (g : GraphCoordinates l E b o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SpTowerShriek.push l E b (o.geometry f) ⋙
        (g.presentation Y).functor.mapDerivedCategory ≅
      (g.presentation X).functor.mapDerivedCategory ⋙
        VaryingRing.P (graphRings l E) (graphTransitions l E) f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (graphForward l E b o g _ _ (g.push f)) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (semilinear_proper_eq l E f))

/-- The intermediate word in the actual model.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
abbrev modelTowerIntermediate
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :=
  ((VaryingRing.J (graphRings l E) (graphTransitions l E) T.cf.i ⋙
    VaryingRing.J (graphRings l E) (graphTransitions l E) T.q) ⋙
    VaryingRing.P (graphRings l E) (graphTransitions l E) T.p) ⋙
    VaryingRing.P (graphRings l E) (graphTransitions l E) T.cg.g

/-- Compare the four intermediate factors before taking either compositor.
Source: Local pairs, ordinary graph coordinates
(blueprint: def-sp-geometric-tower-intermediate). -/
def towerIntermediateCoordinates
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) :
    towerIntermediate l E b o q T ⋙ (nativeCoordinate l E b o q g Z).functor ≅
      (nativeCoordinate l E b o q g X).functor ⋙ modelTowerIntermediate l E T := by
  let := (q.abelian X).hasDerived
  let := (q.abelian Z).hasDerived
  let := b.realizationAdditive X
  let := b.realizationAdditive Z
  let eX := realization l E b X (q.abelian X)
  let eZ := realization l E b Z (q.abelian Z)
  exact Functor.isoWhiskerLeft (eX.functor ⋙ towerIntermediateSystem l E b o T)
      (Functor.isoWhiskerRight eZ.counitIso (g.presentation Z).functor.mapDerivedCategory ≪≫
        Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft eX.functor
      (pasteEvaluations
        (pasteEvaluations
          (pasteEvaluations (graphSystemOpenCoordinates l E b o g T.cf.i)
            (graphSystemOpenCoordinates l E b o g T.q))
          (graphSystemProperCoordinates l E b o g T.p))
        (graphSystemProperCoordinates l E b o g T.cg.g))

/-- The middle mate, before the two compositors.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
def modelTowerMate
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact h] (T : Compactification.Triangle f h) :
    (VaryingRing.J (graphRings l E) (graphTransitions l E) T.cf.i ⋙
      VaryingRing.P (graphRings l E) (graphTransitions l E) T.cf.g) ⋙
      (VaryingRing.J (graphRings l E) (graphTransitions l E) T.cg.i ⋙
        VaryingRing.P (graphRings l E) (graphTransitions l E) T.cg.g) ⟶
      modelTowerIntermediate l E T := by
  letI : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.q := MorphismProperty.of_isPullback T.isPullback
    (inferInstance : QuasiCompact T.cg.i)
  exact Functor.whiskerLeft (VaryingRing.J (graphRings l E) (graphTransitions l E) T.cf.i)
    (Functor.whiskerRight
      (VaryingRing.gamma (graphRings l E) (graphTransitions l E)
        T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (VaryingRing.P (graphRings l E) (graphTransitions l E) T.cg.g))

/-- The model open and proper compositors, with their named equalities.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
def modelTowerCompositors
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) :
    modelTowerIntermediate l E T ⟶
      VaryingRing.J (graphRings l E) (graphTransitions l E) T.cfg.i ⋙
        VaryingRing.P (graphRings l E) (graphTransitions l E) T.cfg.g :=
  Functor.whiskerRight
    (Functor.whiskerRight
      (VaryingRing.namedJComp (graphRings l E) (graphTransitions l E)
        T.cf.i T.q T.cfg.i T.i_q).hom
      (VaryingRing.P (graphRings l E) (graphTransitions l E) T.p))
    (VaryingRing.P (graphRings l E) (graphTransitions l E) T.cg.g) ≫
  Functor.whiskerLeft (VaryingRing.J (graphRings l E) (graphTransitions l E) T.cfg.i)
    (VaryingRing.namedPComp (graphRings l E) (graphTransitions l E)
      T.p T.cg.g T.cfg.g T.p_g).hom

/-- Transport only the tower mate to the supplied native category.
The fully faithful preimage is determined by its image.
Source: Local pairs, coordinate transport
(blueprint: def-sp-geometric-tower-intermediate). -/
def nativeTowerMate
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact h] (T : Compactification.Triangle f h) :
    F l E b o q T.cf ⋙ F l E b o q T.cg ⟶ towerIntermediate l E b o q T :=
  ((nativeCoordinate l E b o q g Z).fullyFaithfulFunctor.whiskeringRight _).preimage
    ((pasteEvaluations (nativeSupportCoordinates l E b o q g T.cf)
        (nativeSupportCoordinates l E b o q g T.cg)).hom ≫
      Functor.whiskerLeft (nativeCoordinate l E b o q g X).functor
        (modelTowerMate l E T) ≫ (towerIntermediateCoordinates l E b o q g T).inv)

/-- Transport only the two compositors to the supplied native category.
Source: Local pairs, coordinate transport
(blueprint: def-sp-geometric-tower-intermediate). -/
def nativeTowerCompositors
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) :
    towerIntermediate l E b o q T ⟶ F l E b o q T.cfg :=
  ((nativeCoordinate l E b o q g Z).fullyFaithfulFunctor.whiskeringRight _).preimage
    ((towerIntermediateCoordinates l E b o q g T).hom ≫
      Functor.whiskerLeft (nativeCoordinate l E b o q g X).functor
        (modelTowerCompositors l E T) ≫ (nativeSupportCoordinates l E b o q g T.cfg).inv)

/-- Exact open extension in inverse fixed module coordinates.
Source: canonical intrinsic open comparison
(blueprint: def-sp-geometric-tower-intermediate). -/
def finiteOpenFixedCoordinates
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j ⋙
        (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ≅
      (sfIntrinsicDerivedEquivalence U (SpTowerShriek.R l E n)).inverse ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) j).mapDerivedCategory :=
  by
    let EU := sfIntrinsicDerivedEquivalence U (SpTowerShriek.R l E n)
    let EX := sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)
    let J := (openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) j).mapDerivedCategory
    let a : EU.functor ⋙ sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j ≅
        J ⋙ EX.functor :=
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (sfIntrinsicOpenExtensionComparison (SpTowerShriek.R l E n) j) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
    exact Iso.isoInverseComp (G := EU) (Iso.compInverseIso (H := EX) a)

/-- Proper image in inverse fixed module coordinates, using the pinned section map.
Source: canonical intrinsic direct-image comparison
(blueprint: def-sp-geometric-tower-intermediate). -/
def finiteProperFixedCoordinates
    (z : FiniteCoordinates l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).rightDerivedFunctor ⋙
        (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).inverse ≅
      (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        (lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (SpTowerShriek.R l E n))) f).rightDerivedFunctor :=
  Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso (z.direct f n)) _ ≪≫
    Iso.isoInverseComp
      ((sfIntrinsicDerivedDirectImageComparison f (SpTowerShriek.R l E n)).compInverseIso)

/-- The four intermediate factors in fixed module coordinates.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
abbrev finiteTowerIntermediateFixed
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :=
  ((towerJ (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cf.i ⋙
    towerJ (ULift.{u + 1} (SpTowerShriek.R l E n)) T.q) ⋙
    towerP (ULift.{u + 1} (SpTowerShriek.R l E n)) T.p) ⋙
    towerP (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cg.g

/-- Identify each of the four intrinsic finite factors before composing them.
Source: finite coefficient coordinates
(blueprint: def-sp-geometric-tower-intermediate). -/
def finiteTowerIntermediateCoordinates
    (z : FiniteCoordinates l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :
    finiteTowerIntermediate l E T n ≅
      (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        finiteTowerIntermediateFixed l E T n :=
  pasteEvaluations
    (pasteEvaluations
      (pasteEvaluations (finiteOpenFixedCoordinates l E T.cf.i n)
        (finiteOpenFixedCoordinates l E T.q n))
      (finiteProperFixedCoordinates l E z T.p n))
    (finiteProperFixedCoordinates l E z T.cg.g n)

/-- The finite open and proper compositors, independently of the tower mate.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-intermediate). -/
def finiteTowerContraction
    (z : FiniteCoordinates l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (n : ℕ) :
    finiteTowerIntermediate l E T n ≅
      (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) T.cfg :=
  finiteTowerIntermediateCoordinates l E z T n ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (towerOpenComposition (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cf.i T.q ≪≫
            towerOpenCongr (ULift.{u + 1} (SpTowerShriek.R l E n)) T.i_q) _ ) _ ≪≫
        Functor.isoWhiskerLeft _
          ((finiteDirectImageComposition (ULift.{u + 1} (SpTowerShriek.R l E n))
            T.p T.cg.g).symm ≪≫
            eqToIso (congrArg
              (towerP (ULift.{u + 1} (SpTowerShriek.R l E n))) T.p_g)))

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
