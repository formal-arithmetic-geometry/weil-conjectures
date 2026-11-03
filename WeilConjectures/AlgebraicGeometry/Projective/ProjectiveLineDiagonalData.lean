/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFiberFinite
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.ProjectiveSpaceStandardCharts
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Canonical maps for the projective-line diagonal

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-p1-diagonal-integrals.md
(blueprint: lem-amb-p1-diagonal-integrals).

The Boolean indices false and true designate the first and second projection.
The chart and trace below use canonical pullback and derived-adjunction comparisons.
The supported class is specified by the recorded, uniquely determining Kummer boundary.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The projective-line trace along either projection. Transport along its canonical
chart uses the chart's inverse-image/direct-image unit, direct-image composition,
the normalized shifted twist comparison, and the recorded projective-line trace.
Source: blueprint lem-amb-p1-diagonal-integrals, the maps t_{p_a}
(blueprint: lem-amb-p1-diagonal-integrals). -/
def projectiveLineDiagonalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A r).map
      (ordinaryFiniteShiftedLinePullback A N hA (projectiveLineTraceTransport N hN A hA)
        e.hom (by
          simpa using hS.map
            ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom)).hom ≫
    ordinaryFiniteProjectiveLineTrace N hN A hA (ProjectiveLine S)
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)

/-- Transport direct image along a product projection to the standard projective line.
This is exactly the prefix of `projectiveLineDiagonalTrace`, before its trace factor.
Source: blueprint lem-amb-p1-diagonal-integrals, proof step 1
(blueprint: def-amb-p1-diagonal-data). -/
def projectiveLineDiagonalChartPushforward (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A r).map
      (ordinaryFiniteShiftedLinePullback A N hA (projectiveLineTraceTransport N hN A hA)
        e.hom (by
          simpa using hS.map
            ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom)).hom

/-- The diagonal trace is the chart pushforward followed by the projective-line trace.
Source: blueprint lem-amb-p1-diagonal-integrals, the maps t_{p_a}
(blueprint: def-amb-p1-diagonal-data).
Proof: unfold both definitions; the two composites agree up to associativity. -/
theorem projectiveLineDiagonalTrace_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    letI : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    letI : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
    projectiveLineDiagonalTrace N hN A hA S hS a =
      projectiveLineDiagonalChartPushforward N hN A hA S hS a ≫
        ordinaryFiniteProjectiveLineTrace N hN A hA (ProjectiveLine S)
          (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) := by
  simp only [projectiveLineDiagonalTrace, projectiveLineDiagonalChartPushforward,
    Category.assoc]

end AlgebraicGeometry.Etale
