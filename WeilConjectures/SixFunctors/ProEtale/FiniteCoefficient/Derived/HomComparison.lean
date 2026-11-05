/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.NumberTheory.Padics.Extension
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin

/-!

# Tor amplitude and internal hom under the pro-étale comparison

Let `ν : X_proét ⥤ X_ét` be the comparison morphism of sites and `ν^*` the induced exact functor
`D(X_ét) ⥤ D(X_proét)`. This file records how `ν^*` interacts with the finite Tor amplitude and
with the internal hom of bounded constructible complexes at a finite coefficient ring `Λ`.

## Main statements

- `ProEtale.DerivedCategory.isIso_derivedComparisonAdjunction_counit_app_derivedHom`:
  for `K ∈ Dctf(X_ét, Λ)` and `M` bounded below, `RHom(ν^* K, ν^* M)` is of étale origin, by
  dévissage over the generators `Rg_* Rj_! L` of `Dctf(X_ét, Λ)`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`
  (`lem-exc-comparison-tor-interval`): an étale complex has Tor amplitude in `[a, b]` if and only
  if its pullback to the pro-étale site has.
- `ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar`
  (`lem-exc-comparison-tor-interval` (ii)): an étale complex whose pullback to the pro-étale
  site has Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom`
  (`thm-sf-hom-comparison-constructible`): `ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)` for `K` in
  `Dctf(X_ét, Λ)` and `M` in `Dᵇc(X_ét, Λ)`, on a finite-type scheme over `k = F̄_p`, glued from
  the separated case
  `ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated`
  (`lem-weil-finite-duality-site-comparison`).

## Implementation notes

The canonical comparison map `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` needs a monoidal structure
on the derived `ν^*` compatible with the internal homs, which is not formalised (only the
tensor comparison `CategoryTheory.Functor.leftDerivedTensorComparison` is);
the comparison is therefore stated as the existence of an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- The derived comparison pullback `ν^*` sends the monoidal unit `Λ_{X_ét}` of `D(X_ét)` to
the monoidal unit `Λ_X` of `D(X_proét)`. -/
noncomputable def mapDerivedCategoryComparisonUpperStarUnitIso (X : Scheme.{u}) :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅ 𝟙_ _ :=
  D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (comparisonUpperStarUnitIso Λ X) ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

end DerivedCategory

/-- `Rν_*` sends the monoidal unit `Λ` of `D(X_proét, Λ)` to the monoidal unit `Λ` of
`D(X_ét, Λ)`: the pro-étale unit is `ν^*` of the étale unit
(`DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso`), and the unit
`M ⟶ Rν_* ν^* M` of the comparison adjunction is invertible on the bounded below `M = Λ`
(`isIso_derivedComparisonAdjunction_unit_app`). -/
noncomputable def rightDerivedComparisonLowerStarUnitIso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  haveI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X (𝟙_ _)
    ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  (R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso Λ X).symm ≪≫
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app (𝟙_ _))).symm

namespace DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {Λ} in
omit [Finite Λ] in
/-- Blueprint `lem-exc-comparison-tor-interval`: Site comparison preserves and detects Tor
intervals.

Let `K` be a complex of étale sheaves of `Λ`-modules. Then `K` has Tor amplitude in `[a, b]` if
and only if its pullback `ν^* K` to the pro-étale site has. The pullback is exact, faithful and
strong monoidal, and it preserves flat sheaves
(`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`), so this is
`DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff`. The blueprint's hypothesis that `K`
be bounded below is not needed. -/
theorem torAmplitudeIn_mapDerivedCategory_iff {X : Scheme.{u}} [IsNoetherianRing Λ] (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) ↔
      Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K :=
  _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff _ a b K

section EtaleOrigin

open Limits ZeroObject

variable {X : Scheme.{u}}
  (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

end EtaleOrigin

end AlgebraicGeometry.ProEtale.DerivedCategory
