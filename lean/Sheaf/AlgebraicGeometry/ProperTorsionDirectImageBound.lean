/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Proper direct-image bound for torsion étale sheaves

Source: Stacks Project, Etale Cohomology, Tag 095U,
lemma-cohomological-dimension-proper (blueprint: lem-kun-proper-torsion-cd-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tag 095U, lemma-cohomological-dimension-proper
(blueprint: lem-kun-proper-torsion-cd-bound). For a proper morphism with fibre dimensions
at most `d`, every torsion abelian étale sheaf has zero higher direct image above `2 * d`.

Proof plan:
1. At a geometric point of `Y`, proper base change and preservation of fibre dimension
   identify the geometric fibre as a finite-type scheme of dimension at most `d` over
   an algebraically closed field (lem-pc-proper-base-change,
   lem-sc-fibre-dimension-after-base-change,
   lem-weil-pbc-dimension-supremum-local-dimensions).
2. Inverse-image stalks identify the pulled-back sheaf as torsion
   (lem-weil-pbc-inverse-image-stalk-germ, lem-weil-pbc-torsion-sheaf-characterizations).
3. For an empty geometric fibre the empty-cover sheaf axiom makes sections zero;
   applying sections to an injective resolution gives zero cohomology in every degree.
4. Otherwise its dimension is a finite integer `e ≤ d`. An algebraically closed field
   is separably closed, hence has torsion cohomological dimension zero
   (lem-kun-03qu-sep-closed). The finite-type torsion cohomological dimension theorem
   thm-sc-finite-type-torsion-cd gives vanishing above `2 * e`, hence above `2 * d`.
5. Bounded-below proper base change (thm-weil-pbc-bounded-below), exact inverse image
   (prop-weil-pbc-inverse-image-exact), and exact sections over the geometric point
   identify the stalk of the higher direct image with this fibre cohomology
   (lem-weil-pbc-geometric-point-pullback-stalk, def-weil-pbc-direct-image,
   def-weil-pbc-etale-cohomology).
6. Every geometric stalk is zero, so geometric-stalk conservativity
   (lemma-weil-pbc-geometric-stalk-conservative) makes the higher direct image zero.
   This also applies when `Y` is empty. -/
theorem isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) (q : ℤ) (hq : 2 * (d : ℤ) < q) :
    IsZero
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
