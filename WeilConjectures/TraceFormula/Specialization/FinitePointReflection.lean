/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOverField
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# Reflection of bounded constructibility along a finite morphism to a separably closed point

Let `k` be a separably closed field and `p : Y ⟶ Spec k` a finite morphism, so that `Y` is a finite
discrete scheme whose residue fields `κ(x)` are finite, hence purely inseparable, over `k`, and
separably closed. A complex `K` of `Λ`-modules on `Y_proét` whose derived pushforward `Rp_* K` is
bounded constructible is itself bounded constructible
(`boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite`).

The proof works with the points `x : Spec κ(x) ⟶ Y`, which are closed immersions:
* a module object `F` on `Y` is the direct sum `⨁ₓ x_* x^* F`
  (`ProEtale.CondensedRing.isIso_biproduct_lift_unit_app_fromSpecResidueField`), since the
  pullbacks to the points jointly reflect isomorphisms and `y^* x_* = 0` for `x ≠ y`; hence
  `(x ≫ p)_* x^* F` is a retract of `p_* F`;
* along the morphism `x ≫ p : Spec κ(x) ⟶ Spec k` of separably closed points the pullback is an
  equivalence (`ProEtale.CondensedRing.isEquivalence_upperStar_of_isField`), both categories being
  equivalent to condensed `Λ`-modules;
* a retract of a finitely presented module is finitely presented when the regular module is
  projective (`CategoryTheory.Mod.IsFinitelyPresented.of_retract`), as it is on `Spec k`.
So `p_*` is conservative and `F` is constructible (for the stratification by points) as soon as
`p_* F` is finitely presented; since `p_*` is exact, `Hⁿ(Rp_* K) ≅ p_* Hⁿ(K)`.

The equivalence of `Mod_{Spec Ω}` with condensed `Λ`-modules for separably closed `Ω` is
`ProEtale.CondensedRing.isEquivalence_upperStarFromPointMod`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]

end Mod
namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

end Limits

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Discrete

variable {Y : Scheme.{u}} [DiscreteTopology Y]

variable [Finite Y]

end Discrete
section FiniteOverPoint

variable {k : Type u} [Field k] [IsSepClosed k] {Y : Scheme.{u}}

end FiniteOverPoint

end AlgebraicGeometry.ProEtale.CondensedRing
