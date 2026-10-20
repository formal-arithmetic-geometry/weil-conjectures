/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

/-!
# Projection on constant coefficients for coproduct-preserving compact support

Source: Stacks Project, Cohomology on Sites, projection formula and generation by
free coefficient complexes.
(blueprint: lem-exc-proetale-constant-support-projection)

Proof: compare the two exact coproduct-preserving coefficient functors, check the
projection on the tensor unit, and extend across the localizing generators of the derived
module category.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Abelian Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace ProEtale

noncomputable instance preservesFiniteLimits_constantSheaf_proetale
    (Y : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    PreservesFiniteLimits
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) := by
  apply comp_preservesFiniteLimits


/-- Constant coefficient complexes satisfy compact-support projection.
Source: Stacks Tags 07A4 and 0G7E.
(blueprint: lem-exc-proetale-constant-support-projection)

Proof: the two sides are exact triangulated coproduct-preserving functors of the coefficient
complex. The projection is an isomorphism at the tensor unit; localizing generation by the
regular module extends this to all coefficients. -/
theorem isIso_constantSupportProjection
    (R₀ : Type (u + 1)) [CommRing R₀] [IsNoetherianRing R₀]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R₀) c)]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R₀)))
    (M : DerivedCategory (ModuleCat.{u + 1} R₀)) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R₀) c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R₀) c.i).mapDerivedCategory.obj K)).app
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapDerivedCategory.obj M)) := by
  sorry

end ProEtale
end AlgebraicGeometry
