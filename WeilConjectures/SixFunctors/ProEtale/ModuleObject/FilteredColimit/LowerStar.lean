/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ModuleForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FilteredColimit.RightDerivedFunctor

/-!
# Derived pushforward of module objects with finite coefficients commutes with filtered colimits

Let `T` be a finite discrete commutative ring, `Λ = T̲` the condensed ring of continuous maps to
`T` (`Profinite.continuousMapRingObj T`), and `f : X ⟶ Y` a quasi-compact quasi-separated
morphism of schemes. We show that the derived pushforward `R((f)_*⟦Λ⟧)` of module objects over
`Λ_X` commutes with filtered colimits of uniformly bounded below complexes, on cohomology
(`ProEtale.CondensedRing.isColimit_mapCocone_homologyFunctor_rightDerivedFunctor_lowerStar`).

The coefficient ring `Λ_X` is torsion, hence not flat over `ℤ`, so the underlying abelian sheaf of
an injective `Λ_X`-module need not be injective. It is however acyclic for the pushforward of
abelian sheaves (`AlgebraicGeometry.ProEtale.CondensedRing.rightAcyclic_lowerStar_forget_obj`):
through the equivalence `ProEtale.finiteCoefficientModEquivalence` with sheaves of
`T`-modules, it is the restriction of scalars along `ℤ → T` of an injective sheaf of `T`-modules,
which is acyclic for the pushforward of sheaves of `ℤ`-modules
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_restrictScalars_obj`), and sheaves of
`ℤ`-modules compute the same higher direct images as abelian sheaves
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarSheafComposeForget₂Iso`). Hence the higher
direct images of module objects are those of the underlying abelian sheaves
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStarForgetIso`), and they commute with
filtered colimits (`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`),
the forgetful functor preserving and reflecting filtered colimits. We conclude by the
general statement
`CategoryTheory.Functor.isColimit_mapCocone_Q_comp_rightDerivedFunctor_comp_homologyFunctor`.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (f : X ⟶ Y)

variable [QuasiCompact f] [QuasiSeparated f]

end AlgebraicGeometry.ProEtale.CondensedRing
