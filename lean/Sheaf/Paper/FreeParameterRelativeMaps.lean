/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.Paper.FreeParameterEvaluationData
public import Sheaf.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-relative-maps). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The free map on an arbitrary relative parameter arrow, using the dependency's
actual generator-preserving free identifications.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def relativeFreeMap (V : Scheme.{u}) (P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X V P)
    (G' : ProfiniteFreeSlice.Comparison R.X V P')
    (a : testScheme V P' ⟶ testScheme V P)
    (ha : a ≫ projection V P = projection V P') :
    ProfiniteFreeSlice.pulledFree R.X V P' ⟶ ProfiniteFreeSlice.pulledFree R.X V P :=
  G'.freeIso.hom ≫ (ProfiniteFreeSlice.localFree R.X V).map
    ((Scheme.ProEt.topology V).uliftYoneda.map (MorphismProperty.Over.homMk a ha)) ≫
      G.freeIso.inv

/-- H(a,-) is precomposition in the existing closed derived Hom.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def schemeParameterMap (V : Scheme.{u}) (P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X V P)
    (G' : ProfiniteFreeSlice.Comparison R.X V P')
    (a : testScheme V P' ⟶ testScheme V P)
    (ha : a ≫ projection V P = projection V P') :
    schemeFunctions R V P ⟶ schemeFunctions R V P' :=
  MonoidalClosed.pre ((DerivedCategory.singleFunctor (Modules R V) 0).map
    (relativeFreeMap R V P P' G G' a ha))

/-- Canonical adjunction construction for parameter restriction and base change.
Source: Stacks 07A7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def squarePullIso {X Y : Scheme.{u}} (f : Y ⟶ X) (P P' : Profinite.{u})
    (h : testScheme Y P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection Y P' ≫ f) :
    (CondensedRing.upperStar R.X f).mapDerivedCategory ⋙
        (CondensedRing.upperStar R.X (projection Y P')).mapDerivedCategory ≅
      (CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory ⋙
        (CondensedRing.upperStar R.X h).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar R.X f)
    (CondensedRing.upperStar R.X (projection Y P'))).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    ((CondensedRing.upperStarComp R.X (projection Y P') f).symm ≪≫
      eqToIso (congrArg (CondensedRing.upperStar R.X) comm.symm) ≪≫
      CondensedRing.upperStarComp R.X h (projection X P)) ≪≫
  Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar R.X (projection X P))
    (CondensedRing.upperStar R.X h)

/-- Canonical adjunction construction for parameter restriction and base change.
Source: Stacks 07A7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def pushSquareApp {X Y : Scheme.{u}} (f : Y ⟶ X) (P P' : Profinite.{u})
    (h : testScheme Y P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection Y P' ≫ f)
    (N : DerivedCategory (Modules R (testScheme X P))) :
    (CondensedRing.upperStar R.X f).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj N) ⟶
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection Y P')).obj
      ((CondensedRing.upperStar R.X h).mapDerivedCategory.obj N) :=
  (projectionAdjunction R Y P').homEquiv _ _
    ((squarePullIso R f P P' h comm).hom.app _ ≫
      (CondensedRing.upperStar R.X h).mapDerivedCategory.map
        ((projectionAdjunction R X P).counit.app N))

/-- Canonical adjunction construction for parameter restriction and base change.
Source: Stacks 07A7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def parameterBaseMap {X Y : Scheme.{u}} (f : Y ⟶ X) (P : Profinite.{u}) :
    testScheme Y P ⟶ testScheme X P :=
  pullback.lift (pullback.fst _ _) (projection Y P ≫ f)
    (specULiftZIsTerminal.hom_ext _ _)

/-- Canonical adjunction construction for parameter restriction and base change.
Source: Stacks 07A7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def pushParameterApp (X : Scheme.{u}) (P P' : Profinite.{u})
    (h : testScheme X P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection X P')
    (N : DerivedCategory (Modules R X)) :
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
      ((CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory.obj N) ⟶
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P')).obj
      ((CondensedRing.upperStar R.X (projection X P')).mapDerivedCategory.obj N) :=
  (projectionAdjunction R X P').homEquiv _ _
    ((Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp R.X h (projection X P)).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar R.X) comm))).inv.app _ ≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar R.X (projection X P))
      (CondensedRing.upperStar R.X h)).hom.app _ ≫
    (CondensedRing.upperStar R.X h).mapDerivedCategory.map
      ((projectionAdjunction R X P).counit.app
        ((CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory.obj N)) ≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar R.X (projection X P))
      (CondensedRing.upperStar R.X h)).inv.app N ≫
    (Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp R.X h (projection X P)).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar R.X) comm))).hom.app N)

/-- Parameter maps at the condensed point are the free functor on h_j.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def pointParameterMap {P P' : Profinite.{u}} (j : P' ⟶ P) :
    functions R P ⟶ functions R P' :=
  MonoidalClosed.pre ((DerivedCategory.singleFunctor (PointModules R) 0).map
    ((Profinite.CondensedAction.InternalBar.free (Mon.mk R.X)).map
      ((coherentTopology Profinite).uliftYoneda.map j)))

/-- The relative scheme map associated to a continuous parameter map.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-relative-maps). -/
abbrev testSchemeMap (X : Scheme.{u}) {P P' : Profinite.{u}} (j : P' ⟶ P) :=
  ((profiniteToProEtOf X).map j).left

/-- The whole-family relative map (q,p') ↦ (q,alpha(q,p')) over V = X[Q]. The functor
P ↦ Spec C(P,ℤ) preserves finite limits because the locally-constant-function functor is
a right adjoint (Stacks 097D) and Spec is a right adjoint, so the product comparison is
invertible. The map lies over V by the second pullback equation.
Source: Stacks 08J7 and 097D (blueprint: def-sfb-free-parameter-relative-maps). -/
def familyParameterMap (X : Scheme.{u}) (Q P P' : Profinite.{u})
    (α : Q ⨯ P' ⟶ P) :
    testScheme (testScheme X Q) P' ⟶ testScheme (testScheme X Q) P :=
  haveI : profiniteToCommRingCatOp.{u}.IsRightAdjoint := profiniteToCommRingCatOp_isRightAdjoint
  haveI : PreservesFiniteLimits profiniteToScheme.{u} :=
    inferInstanceAs (PreservesFiniteLimits (profiniteToCommRingCatOp.{u} ⋙ Scheme.Spec))
  pullback.lift
    (Limits.prod.lift (projection (testScheme X Q) P' ≫ pullback.fst _ _)
      (pullback.fst _ _) ≫ inv (Limits.prodComparison profiniteToScheme Q P') ≫
        profiniteToScheme.map α)
    (projection (testScheme X Q) P') (specULiftZIsTerminal.hom_ext _ _)

/-- The F-action is defined using beta and H, independently of c.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-relative-maps). -/
def conjugatedAction (V : Scheme.{u}) (P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X V P)
    (G' : ProfiniteFreeSlice.Comparison R.X V P')
    (a : testScheme V P' ⟶ testScheme V P)
    (ha : a ≫ projection V P = projection V P')
    (N N' : DerivedCategory (PointModules R))
    (v : (pointPullD R V).obj N ⟶ (pointPullD R V).obj N')
    [IsIso (beta R V P N)] [IsIso (beta R V P' N')] :=
  beta R V P N ≫ (schemeParameterMap R V P P' G G' a ha).app _ ≫
    (schemeFunctions R V P').map v ≫ inv (beta R V P' N')

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
