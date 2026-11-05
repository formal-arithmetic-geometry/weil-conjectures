/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# Proper base change for module objects with finite coefficients

Let `T` be a finite discrete commutative ring, `T̲ = C(-, T)` its condensed ring and
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` the comparison of the derived category of
module objects over `T̲_X` with that of pro-étale sheaves of `T`-modules. Call a complex `C` of
module objects *bounded below of étale origin* if `Φ C` is
(`ProEtale.DerivedCategory.plusEtaleOrigin`).

* Direct images along quasi-compact quasi-separated morphisms preserve complexes bounded below of
  étale origin
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj`).
* **Proper base change**: for a cartesian square with proper `f`, the base change morphism
  `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over `T̲` is invertible at every `M` bounded
  below of étale origin
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_finiteCoefficient`).
  This is the finite-level pro-étale proper base change
  (`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`, blueprint
  `thm-weil-pbc-finite-level-proetale`) read through `Φ`
  (`ProEtale.isIso_baseChangeMap_app_finiteCoefficient_iff`). No hypothesis is made on `g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

namespace CondensedRing

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

end CondensedRing

end AlgebraicGeometry.ProEtale
