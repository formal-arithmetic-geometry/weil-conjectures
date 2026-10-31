/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DlConstantFieldCharts
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedExchange
public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.RealSheavesSetup
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent
import WeilConjectures.CategoryTheory.ExactInputDerivedTransformation
import WeilConjectures.AlgebraicGeometry.CondensedLocalFrobeniusPowers
import WeilConjectures.AlgebraicGeometry.CondensedFibresExact

import WeilConjectures.AlgebraicGeometry.ClosedPointField
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.LinearAlgebra.PowerSpectrumConjugation

/-! # Pointed charts for ordinary condensed boundary cohomology

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-exact,
p-dl-a1-exact.proof.md, Steps 2--4; Stacks 04KV, 03CF and 08FI
(blueprint: lem-dl-a1-condensed-boundary-charts).

Only the geometric chart structure is reused from the older chart module. Every module,
derived functor, Weil structure and scalar fibre below is the ordinary condensed one.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option genSizeOf false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedBoundary

variable (l : ℕ) [Fact l.Prime]

/-- The scalar-fibre identification along pullback is the inverse compositor followed by
the equality of the two geometric points. Applying `singleFunctor` gives its degree-zero
derived identification, with no new choice of a fibre map.
Source: latest blueprint, Steps 2--4, corresponding geometric fibres
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
def fibrePullIso (K : Type u) [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (h : Y ⟶ X) (zY : Spec (.of K) ⟶ Y)
    (zX : Spec (.of K) ⟶ X) (hz : zY ≫ h = zX)
    (M : CondensedModule.Modules l X) :
    (CondensedQbarGeometricEvaluation.fieldFiber K l).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) zY).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).obj M)) ≅
      (CondensedQbarGeometricEvaluation.fieldFiber K l).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) zX).obj M) :=
  (CondensedQbarGeometricEvaluation.fieldFiber K l).mapIso
    (((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) zY h).app M).symm ≪≫
      eqToIso (congrArg
        (fun f ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) hz))

/-- The canonical exchange mate, transported through the exact-pullback identification.
Source: latest blueprint, Steps 2--4; Stacks 03CF, 08FI
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
@[irreducible] def exchange {U W UV V : Scheme.{u}} {j : U ⟶ W} {h : V ⟶ W}
    {jV : UV ⟶ V} {hU : UV ⟶ U} (sq : CommSq hU jV j h) :
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).mapDerivedCategory ⟶
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) hU).mapDerivedCategory ⋙
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor :=
  (Functor.isoWhiskerLeft _
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) h).symm).hom ≫
    CondensedRing.moduleObjectDerivedExchange (Profinite.padicAlgClRingObj l) sq ≫
      (Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.padicAlgClRingObj l) hU) _).hom

/-- The cohomology arrow is induced by this same mate, after exact pullback commutes with
cohomology; it is not an independently chosen degreewise comparison.
Source: latest blueprint, Steps 2--4, cohomology paragraph
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
@[irreducible] def cohomologyExchange {U W UV V : Scheme.{u}} {j : U ⟶ W} {h : V ⟶ W}
    {jV : UV ⟶ V} {hU : UV ⟶ U} (sq : CommSq hU jV j h)
    (n : ℤ) (K : DerivedCategory (CondensedModule.Modules l U)) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).obj
        ((DerivedCategory.homologyFunctor (CondensedModule.Modules l W) n).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor.obj K)) ⟶
      (DerivedCategory.homologyFunctor (CondensedModule.Modules l V) n).obj
        (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) hU).mapDerivedCategory ⋙
          (CondensedRing.lowerStar
            (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor).obj K) :=
  ((CondensedRing.upperStar
    (Profinite.padicAlgClRingObj l) h).mapDerivedCategoryHomologyFunctorIso n).hom.app
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor.obj K) ≫
    (DerivedCategory.homologyFunctor (CondensedModule.Modules l V) n).map ((exchange l sq).app K)

variable (D E : FiniteFieldDatum.{u})

/-- Restriction of degree-zero fixed pairs. The carrier comparison specifies the action
on objects and arrows, and the equation specifies precisely the iterated Weil structure.
Source: latest blueprint, Steps 2--4, displayed theta^[d]
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
structure WeilRestriction
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (d : ℕ) (h : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left)
    (ret : (E.geometricFrobenius Y).hom ≫ h =
      h ≫ localPositivePower (D.geometricFrobenius X).hom (d - 1)) where
  pull : CondensedWeil.WeilModule D l X ⥤ CondensedWeil.WeilModule E l Y
  carrier : pull ⋙ Endofunctor.IsoAlgebra.forget _ ≅
    Endofunctor.IsoAlgebra.forget _ ⋙
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h
  weil : ∀ M : CondensedWeil.WeilModule D l X,
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (E.geometricFrobenius Y).hom).map (carrier.hom.app M) ≫
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
        (E.geometricFrobenius Y).hom h).inv.app M.carrier ≫
      eqToHom (congrArg
        (fun f ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M.carrier)
        ret) ≫
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) h
        (localPositivePower (D.geometricFrobenius X).hom (d - 1))).hom.app M.carrier ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).map
        (CondensedWeil.iterate (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X).hom M.carrier M.str (d - 1)).hom =
      (pull.obj M).str.hom ≫ carrier.hom.app M

variable {D E}

/-- Local spectra for the actual scalar fibres at all geometric lifts. The exponent is
the relative residue degree, and is allowed to exceed the degree of the constant extension.
Source: latest blueprint, Steps 2--4, local Frobenius paragraph
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
def LocalPower (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (M : CondensedWeil.WeilModule D l X) (N : CondensedWeil.WeilModule E l Y)
    (x : closedPoints X.left) (y : closedPoints Y.left) (e : ℕ) : Prop :=
  ∀ (i : X.left.residueField x.val →+* D.k)
    (hi : i.comp (X.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (i' : Y.left.residueField y.val →+* E.k)
    (hi' : i'.comp (Y.hom.residueFieldAlgebraMap y.val) = algebraMap E.k₀ E.k),
    (∃ a : CondensedWeil.closedFiber D l X M x i hi ≅
        CondensedWeil.closedFiber E l Y N y i' hi',
      a.hom ≫ CondensedWeil.closedOperator E l Y N y i' hi' =
        ((CondensedWeil.closedOperator D l X M x i hi) ^ e) ≫ a.hom) ∧
    ∀ α : PadicAlgCl l,
    Module.End.HasEigenvalue (CondensedWeil.closedOperator E l Y N y i' hi').hom α ↔
      ∃ β : PadicAlgCl l,
        Module.End.HasEigenvalue (CondensedWeil.closedOperator D l X M x i hi).hom β ∧
          α = β ^ e

variable (D)

/-- The ordinary derived exchange assertions, including its prescribed shifts, triangles,
cohomology maps and connecting squares. Shift structures on right derivation are normalized
by the computation units, so these fields do not choose arbitrary triangle conventions.
Source: latest blueprint, Steps 2--4; Stacks 08FI
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
structure DerivedExchange {U W UV V : Scheme.{u}} {j : U ⟶ W} {h : V ⟶ W}
    {jV : UV ⟶ V} {hU : UV ⟶ U} (sq : CommSq hU jV j h) where
  [shiftJ : (CondensedRing.lowerStar
    (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor.CommShift ℤ]
  [shiftJV : (CondensedRing.lowerStar
    (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor.CommShift ℤ]
  normalizedJ : NatTrans.CommShift
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) j).rightDerivedFunctorUnit ℤ
  normalizedJV : NatTrans.CommShift
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctorUnit ℤ
  triangulatedJ : (CondensedRing.lowerStar
    (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor.IsTriangulated
  triangulatedJV : (CondensedRing.lowerStar
    (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor.IsTriangulated
  shift : NatTrans.CommShift (exchange l sq) ℤ
  iso : ∀ K : DerivedCategory (CondensedModule.Modules l U),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U K →
      IsIso ((exchange l sq).app K)
  triangles : ∀ T : Triangle (DerivedCategory (CondensedModule.Modules l U)),
    T ∈ distTriang _ →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U T.obj₁ →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U T.obj₂ →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U T.obj₃ →
    ∃ e : (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor ⋙
        (CondensedRing.upperStar
          (Profinite.padicAlgClRingObj l) h).mapDerivedCategory).mapTriangle.obj T) ≅
      (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) hU).mapDerivedCategory ⋙
        (CondensedRing.lowerStar
          (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor).mapTriangle.obj T),
      e.hom.hom₁ = (exchange l sq).app T.obj₁ ∧
      e.hom.hom₂ = (exchange l sq).app T.obj₂ ∧
      e.hom.hom₃ = (exchange l sq).app T.obj₃
  cohomology : ∀ (n : ℤ) (K : DerivedCategory (CondensedModule.Modules l U)),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U K →
      IsIso (cohomologyExchange l sq n K)
  connecting : ∀ (T : Triangle (DerivedCategory (CondensedModule.Modules l U))), T ∈ distTriang _ →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U T.obj₁ →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U T.obj₂ →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) U T.obj₃ →
    ∀ n : ℤ,
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).map
        ((DerivedCategory.homologyFunctor (CondensedModule.Modules l W) 0).shiftMap
          ((CondensedRing.lowerStar
            (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor.map T.mor₃ ≫
            ((CondensedRing.lowerStar
              (Profinite.padicAlgClRingObj l) j).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
                T.obj₁)
          n (n + 1) (add_comm 1 n)) ≫ cohomologyExchange l sq (n + 1) T.obj₁ =
        cohomologyExchange l sq n T.obj₃ ≫
          (DerivedCategory.homologyFunctor (CondensedModule.Modules l V) 0).shiftMap
            (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) hU).mapDerivedCategory ⋙
              (CondensedRing.lowerStar
                (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor).map T.mor₃ ≫
              (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) hU).mapDerivedCategory ⋙
                (CondensedRing.lowerStar
                  (Profinite.padicAlgClRingObj l) jV).rightDerivedFunctor).commShiftIso
                (1 : ℤ)).hom.app T.obj₁)
            n (n + 1) (add_comm 1 n)

/-- Properties of the actual restriction functor, bundled before specializing to the
finite-extension chart to keep the dependent chart type small.
Source: latest blueprint, Steps 2--4, exactness, lissity and weights
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
structure PullbackProperties (E : FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (d : ℕ) (h : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left)
    (ret : (E.geometricFrobenius Y).hom ≫ h =
      h ≫ localPositivePower (D.geometricFrobenius X).hom (d - 1))
    (R : WeilRestriction l D E X Y d h ret) where
  constructible : ∀ M : CondensedWeil.WeilModule D l X,
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X).left M.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (E.geometricFiber Y).left (R.pull.obj M).carrier
  exact : PreservesFiniteLimits
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h) ∧
    PreservesFiniteColimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h)
  lisse : ∀ M : CondensedModule.Modules l (D.geometricFiber X).left,
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).obj M)
  pure : ∀ (M : CondensedWeil.WeilModule D l X),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier →
    ∀ (iota : PadicAlgCl l →+* ℂ) (w : ℝ),
      CondensedWeil.Pure D l X M iota w → CondensedWeil.Pure E l Y (R.pull.obj M) iota w

/-- Boundary comparison with a specified common closure. At the constant-field chart
`field` is reflexivity, so the displayed pullback map is exactly `fibrePullIso`.
Source: latest blueprint, Steps 2--4, rational lift and its Frobenius
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
@[irreducible] def BoundaryComparison (E : FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (d : ℕ) (h : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left)
    (ret : (E.geometricFrobenius Y).hom ≫ h =
      h ≫ localPositivePower (D.geometricFrobenius X).hom (d - 1))
    (R : WeilRestriction l D E X Y d h ret) (s : closedPoints X.left)
    (t : closedPoints Y.left) (field : CommRingCat.of E.k = CommRingCat.of D.k) : Prop :=
  Nat.card (Y.left.residueField t.val) = Nat.card (X.left.residueField s.val) ∧
  ∀ M : CondensedWeil.WeilModule D l X,
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X).left M.carrier →
    ∀ (is : X.left.residueField s.val →+* D.k)
      (hs : is.comp (X.hom.residueFieldAlgebraMap s.val) = algebraMap D.k₀ D.k)
      (it : Y.left.residueField t.val →+* E.k)
      (ht : it.comp (Y.hom.residueFieldAlgebraMap t.val) = algebraMap E.k₀ E.k),
    ∃ e : CondensedWeil.closedFiber D l X M s is hs ≅
      CondensedWeil.closedFiber E l Y (R.pull.obj M) t it ht,
      e.hom ≫ CondensedWeil.closedOperator E l Y (R.pull.obj M) t it ht =
        CondensedWeil.closedOperator D l X M s is hs ≫ e.hom ∧
      ∀ hz : (Spec.map (eqToHom field) ≫ localClosedPoint E Y t it ht) ≫ h =
          localClosedPoint D X s is hs,
        HEq e.symm
          ((CondensedQbarGeometricEvaluation.fieldFiber D.k l).mapIso
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
              (Spec.map (eqToHom field) ≫ localClosedPoint E Y t it ht)).mapIso
                (R.carrier.app M)) ≪≫
            fibrePullIso l D.k h
              (Spec.map (eqToHom field) ≫ localClosedPoint E Y t it ht)
              (localClosedPoint D X s is hs) hz M.carrier)

/-- Relative residue-degree spectra for a specified finite-base map.
Source: latest blueprint, Steps 2--4, local spectra and residue cardinalities
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
structure SpectrumComparison (E : FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) (Y : Over (Spec (.of E.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (d : ℕ) (h : (E.geometricFiber Y).left ⟶ (D.geometricFiber X).left)
    (ret : (E.geometricFrobenius Y).hom ≫ h =
      h ≫ localPositivePower (D.geometricFrobenius X).hom (d - 1))
    (R : WeilRestriction l D E X Y d h ret) (h₀ : Y.left ⟶ X.left) where
  spectrum : ∀ (M : CondensedWeil.WeilModule D l X),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier →
    ∀ (x : closedPoints Y.left) (y : closedPoints X.left), h₀ x.val = y.val →
      Nat.card (Y.left.residueField x.val) =
          Nat.card (X.left.residueField y.val) ^ h₀.residueDegree x.val ∧
        LocalPower l X Y M (R.pull.obj M) y x (h₀.residueDegree x.val)

set_option maxHeartbeats 3200000 in
-- Check the chart with the cohomological and fibre clauses bundled separately.
/-- All condensed clauses for the pointed geometric chart. The chart is the connected
component, not an arbitrary neighbourhood; the rational lift has the prescribed residue
embedding, encoded by its equality as a map from Spec(kappa(s)).
Source: latest blueprint, Steps 2--4; Stacks 04KV
(blueprint: lem-dl-a1-condensed-boundary-charts). -/
structure ChartData (c : Scheme.MiddleExtensionCurve D)
    (s : closedPoints c.C.left) (i : c.C.left.residueField s.val →+* D.k)
    (A : DlPointedConstantChart D c s i) where
  component : Set.range A.chart.left =
    connectedComponent (A.chart.left A.t.val)
  degree : A.m = localClosedPointDegree D c.C s
  rationalLift : ∃ t : Spec (c.C.left.residueField s.val) ⟶ A.curve.C.left,
    t (IsLocalRing.closedPoint (c.C.left.residueField s.val)) = A.t.val ∧
    t ≫ A.chart.left ≫ (constantExtensionProjection D A.m A.positive c.C).left =
      c.C.left.fromSpecResidueField s.val ∧
    t ≫ A.curve.C.hom = Spec.map (CommRingCat.ofHom A.residue.symm.toRingHom)
  affineU : IsAffine A.curve.U.left
  closed : IsClosedImmersion A.chart.left
  geometricOpen : IsOpenImmersion (A.geometricMap D)
  geometricClosed : IsClosedImmersion (A.geometricMap D)
  returnC : ((constantExtensionDatum D A.m A.positive).geometricFrobenius
    A.curve.C).hom ≫ A.geometricMap D = A.geometricMap D ≫
        localPositivePower (D.geometricFrobenius c.C).hom (A.m - 1)
  returnU : ((constantExtensionDatum D A.m A.positive).geometricFrobenius
    A.curve.U).hom ≫ A.geometricOpenMap D = A.geometricOpenMap D ≫
        localPositivePower (D.geometricFrobenius c.U).hom (A.m - 1)
  square : IsPullback (A.geometricOpenMap D)
    (zlFiberMap (constantExtensionDatum D A.m A.positive) A.curve.j)
    (zlFiberMap D c.j) (A.geometricMap D)
  restrictC : WeilRestriction l D (constantExtensionDatum D A.m A.positive)
    c.C A.curve.C A.m (A.geometricMap D) returnC
  restrictU : WeilRestriction l D (constantExtensionDatum D A.m A.positive)
    c.U A.curve.U A.m (A.geometricOpenMap D) returnU
  propertiesC : PullbackProperties l D (constantExtensionDatum D A.m A.positive)
    c.C A.curve.C A.m (A.geometricMap D) returnC restrictC
  propertiesU : PullbackProperties l D (constantExtensionDatum D A.m A.positive)
    c.U A.curve.U A.m (A.geometricOpenMap D) returnU restrictU
  derived : DerivedExchange l square.toCommSq
  boundary : BoundaryComparison l D (constantExtensionDatum D A.m A.positive)
    c.C A.curve.C A.m (A.geometricMap D) returnC restrictC s A.t rfl
  localSpectrum : SpectrumComparison l D (constantExtensionDatum D A.m A.positive)
    c.U A.curve.U A.m (A.geometricOpenMap D) returnU restrictU
      (A.openChartU.left ≫ (constantExtensionProjection D A.m A.positive c.U).left)

/-- Pointed constant-field charts for ordinary condensed boundary cohomology.
Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-exact,
p-dl-a1-exact.proof.md, Steps 2--4; Stacks 04KV
(blueprint: lem-dl-a1-condensed-boundary-charts).

Proof (the node's twelve steps): (1) The closed-point field is finite and separable;
form Spec(A tensor kappa(s)) and its canonical rational lift. (2) Noetherianity gives
finitely many irreducible components. Their intersection graph gives clopen connected
components; the component containing the lift is affine by its idempotent. (3) Smooth
relative dimension one and etaleness persist under base change and open restriction.
The rational point gives geometric connectedness by Stacks 04KV. (4) The explicit tensor
associativity isomorphism identifies its geometric fibre with a clopen of W. The d-th
Frobenius fixes the finite constant field and its idempotent. (5) Etale openness gives
density. Smooth connected curves are integral, and their nonempty dense opens are
geometrically connected; their boundary is finite and closed. (6) The coefficient maps
are isomorphisms, so module restriction is exact and preserves finite free local models.
(7) Apply lem-sf-ringed-restriction-exchange-open-descent: on a K-injective I the mate
is the identity I(U times_W E)=I(U_V times_V E), normalized by the counit.
(8) lem-sfb-exact-input-derived-transformation makes this same mate shift compatible
and an isomorphism of image triangles. (9) Exact restriction commutes with cohomology;
lem-weil-pbc-derived-cohomology-ladder gives all connecting squares.
(10) Iterate theta using its actual pullback compositors; naturality gives the functor
on degree-zero fixed pairs. (11) The return-length identity d deg(x)=e deg(y) and
lem-wf-condensed-local-frobenius-powers give the relative residue-degree power and
q_x=q_y^e. (12) At the rational lift the residue degree is one, giving identical local
Frobenius and cardinality. The spectrum of a positive power gives preservation of every
real punctual weight, including zero sheaves and repeated eigenvalues. -/
theorem condensedBoundaryCharts (hl : l ≠ D.p)
    (c : Scheme.MiddleExtensionCurve D) [IsAffine c.C.left]
    [SmoothOfRelativeDimension 1 c.C.hom]
    (s : closedPoints c.C.left) (hs : s.val ∉ Set.range c.j.left)
    (i : c.C.left.residueField s.val →+* D.k)
    (hi : i.comp (c.C.hom.residueFieldAlgebraMap s.val) = algebraMap D.k₀ D.k) :
    ∃ A : DlPointedConstantChart D c s i, Nonempty (ChartData l D c s i A) := by
  sorry

end WeilConjectures.CondensedBoundary
