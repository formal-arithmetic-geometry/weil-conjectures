/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SmoothPurity.CompactificationProjectionComposition
public import WeilConjectures.AlgebraicGeometry.SfIdentityProjectionNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-! # Coherence of the finite small-etale projection transformation

Source: current blueprint, sec-six-functors/sk-prop-sf-pf-coherence,
statement and proof (blueprint: prop-sf-pf-coherence).

All inputs are in the unbounded small-etale derived categories with an arbitrary
finite commutative coefficient ring. The arrows are the canonical proper-counit/open
projection, compact-support exchange, and compactification comparisons. In particular,
reduction by every ideal is allowed without flatness or a Tor hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilConjectures

variable (Λ : Type (u + 1)) [CommRing Λ]

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

/-- Naturality in both inputs, as an equality of the actual projection components.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (a : K ⟶ K')
    {L L' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (b : L ⟶ L') :
    type_of% (projectionMapOfCompactification_naturality (ModuleCat.{u + 1} Λ) c a b) :=
  projectionMapOfCompactification_naturality (ModuleCat.{u + 1} Λ) c a b

/-- The specified common-refinement comparison intertwines the projection maps.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_compactification
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [Finite Λ]
    (c d : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of%
      (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c d K L) :=
  projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c d K L

/-- Proper coincidence through the specified compact-support/direct-image comparison.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_proper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) f K L) :=
  projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) f K L

/-- The displayed Cartesian square, including both tensor and pullback-square comparisons.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_baseChange_finite
    {X' X Y' Y : Scheme.{u}} [Finite Λ] {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq K L) :=
  projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq K L

/-- All-ideal finite reduction: the square is precisely part (1) of the reduction theorem.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_reduction_finite
    {X Y : Scheme.{u}} [Finite Λ] {f : X ⟶ Y} (c : Compactification f) (J : Ideal Λ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMapOfCompactification_constantSingle (ModuleCat.{u + 1} Λ) c
      (ModuleCat.of Λ (Λ ⧸ J)) K L) :=
  projectionMapOfCompactification_constantSingle (ModuleCat.{u + 1} Λ) c
      (ModuleCat.of Λ (Λ ⧸ J)) K L

/-- Composition for every compatible compactification tower, with its specified compositor.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_composition
    {X Y Z : Scheme.{u}} [Finite Λ] (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMapOfCompactification_tower_comp Λ f g d e K L) :=
  projectionMapOfCompactification_tower_comp Λ f g d e K L

/-- The canonical compact-support compositors obey the associativity pentagon.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_pentagon
    {X Y Z T : Scheme.{u}} [Finite Λ]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian T]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] :
    type_of% (unboundedEtaleLowerShriekCompIso_assoc Λ f g h) :=
  unboundedEtaleLowerShriekCompIso_assoc Λ f g h

end WeilConjectures
