/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionGeneral
public import WeilConjectures.TraceFormula.OrdinaryKunnethReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel

/-!
# Vanishing of `Lg'^* Rf^! Rj_!` for smooth `f` and disjoint `g`, `j`

Let `f : X ⟶ Y` be smooth of relative dimension `d`, `g : Y' ⟶ Y` a morphism with base change
`g' : X' ⟶ X` and `j : U ⟶ Y` an open immersion whose image is disjoint from that of `g`. Then
`Lg'^* Rf^! Rj_! M = 0` for every `M`. This is the content of smooth base change for `Rf^!`
along `g` at extensions by zero: `Lg'^* Rf^! Rj_! M ≅ Rf'^! Lg^* Rj_! M = 0`.

The statement only involves objects, not morphisms, so it is transported from finite
coefficients to `𝒪_E` and to `ℚ̄_ℓ` through the (non-canonical) coefficient comparisons:

* `Etale.isZero_leftDerivedUpperStar_obj_rightDerivedUpperShriek_obj_rightDerivedLowerShriek_obj`:
  on the étale site with finite coefficients, from smooth base change
  (`Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`);
* `ProEtale.CondensedRing.isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicIntegers`:
  for bounded constructible `𝒪_E`-complexes, since the reduction modulo `ℓ` commutes with
  `Lg'^*`, `Rf^!` and `Rj_!` (`etaleReductionUpperStarIso`, `hasEtaleReductionLowerShriekIso`)
  and detects zero objects (`isZero_of_isZero_etaleReduction`);
* `ProEtale.CondensedRing.isZero_upperStar_obj_upperShriek_obj_lowerShriek_obj_padicAlgCl`:
  for bounded constructible `ℚ̄_ℓ`-complexes, through integral models
  (`ProEtale.exists_padicAlgCl_iso_integralModel`) and the coefficient comparisons for
  `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
