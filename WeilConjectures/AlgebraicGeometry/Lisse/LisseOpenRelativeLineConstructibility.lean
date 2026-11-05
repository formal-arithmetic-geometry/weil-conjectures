/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
import WeilConjectures.AlgebraicGeometry.Constant.ConstantShriekRelativeDimensionOne
import WeilConjectures.CategoryTheory.Etale.EtaleLisseFiltrationDevissage
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekNaturalSES
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteEtaleFiltration
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-!
# Constructibility for lisse coefficients on an open relative affine line

Source: Stacks Project, Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`, specialized to
finite coefficient rings and affine finite-type integer bases
(blueprint: lem-weil-pbc-etale-lisse-open-relative-line-constructibility).
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

section StableInstances

@[instance_reducible] private noncomputable def stableAbelian
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := inferInstance

attribute [local instance 2000] stableAbelian

@[instance_reducible] private noncomputable def stableDerived
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  unfold stableAbelian
  infer_instance

attribute [local instance 2000] stableDerived

-- Stalk calculation adapted from Bin Wu, FiniteEtaleModuleTraceData.

-- The trace proof tests equality only at algebraically closed stalks.

@[irreducible] private noncomputable def sourceFunctor
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sheaf X.smallEtaleTopology A ⥤ _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  singleZero _ ⋙ shriekFunctor A c

end StableInstances

end AlgebraicGeometry.Etale
