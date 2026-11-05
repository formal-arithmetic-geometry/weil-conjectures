/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.HomFilteredColimitExt
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-!
# Basic objects of `D(X_proét, Λ)` whose morphisms commute with filtered colimits

Let `Λ` be a commutative condensed ring and `X` a scheme, with coefficient ring
`Λ_X = condensedRingObj Λ X`. We show that the following objects `s` of the derived category of
`Λ_X`-modules satisfy `DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}`, i.e. for every
`u + 1`-small filtered colimit `B = colim Bᵢ` of `Λ_X`-modules and every `n`, the map
`colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is bijective (blueprint
`sk-lem-constructible-ext-continuity`, `sk-cor-pe-bounded-continuity`):

* the unit `ℤ` of abelian pro-étale sheaves in degree `0`, for `X` qcqs
  (`AlgebraicGeometry.ProEtale.homCommutesWithFilteredColimits_singleFunctor_unit`): the
  morphisms `ℤ[0] ⟶ B[-q]` are the pro-étale cohomology groups `Hᵠ(X, B)`, which commute with
  filtered colimits (`AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_of_isFiltered_small`);
* the regular module `Λ_X` in degree `0`, for `X` qcqs and `Λ_X` flat
  (`CondensedRing.homCommutesWithFilteredColimits_singleFunctor_regular`):
  `Λ_X = Λ_X ⊗ ℤ` is the free module on the unit, and the free-forgetful adjunction consists of
  exact functors when `Λ_X` is flat, the forgetful functor preserving filtered colimits;
* the extension by zero `j_! s` along an open immersion `j` of an object `s` with this property
  (`CondensedRing.homCommutesWithFilteredColimits_openImmersionLowerShriek`),
  `j_!` and `j^*` being exact and `j^*` a left adjoint;
* a dualizable module `L` in degree `0` as soon as the regular module is
  (`AlgebraicGeometry.ProEtale.homCommutesWithFilteredColimits_singleFunctor_of_isDualizable`),
  via the adjunction `- ⊗ L ⊣ - ⊗ Lᘁ` of exact functors which are both left and right adjoints;
* hence every locally free `Λ_X`-module in degree `0`, for `X` qcqs and `Λ_X` flat
  (`CondensedRing.homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj DerivedCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end CondensedRing

end AlgebraicGeometry.ProEtale
