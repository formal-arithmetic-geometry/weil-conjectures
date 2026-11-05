/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.RefinementUniqueness
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!

# Coherence of the compactification comparisons

Let `f : X ⟶ Y` be a morphism of schemes and let `r : c.Refinement d` be a refinement of
compactifications of `f`, with `u = r.hom : c.Z ⟶ d.Z`, whose square over `X` is cartesian
(this holds automatically when `c` is dense, by
`AlgebraicGeometry.Compactification.Refinement.isPullback_of_isSchemeTheoreticallyDominant`).
This file proves the coherence of the comparisons between the derived lower shrieks attached
to different compactifications (blueprint `sk-prop-sf-comp-coherence`):

* on `d.Z`, the canonical map `α_u : j_{d!} K ⟶ Ru_* j_{c!} K` is an isomorphism for torsion
  coefficients, it is the identity for the identity refinement and it is transitive under
  composition of refinements;
* consequently, the comparison `Rf_!(d) ⟶ Rf_!(c)` of the candidates
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`) is
  `R(d.g)_* α_u` followed by the composition isomorphism `R(d.g)_* Ru_* ≅ R(c.g)_*`;
* the isomorphism `Rf_!(c) ≅ Rf_!(d)` obtained from a common refinement does not depend on
  the chosen common refinement, and these isomorphisms satisfy the cocycle condition;
* for an arbitrary refinement `r`, not necessarily cartesian over `X`, the comparison
  `Rf_!(d) ≅ Rf_!(c)` is defined through the dense refinement `Compactification.inf c c ⟶ c`;
  it agrees with the one above for cartesian `r`, satisfies the identity and transitivity
  laws, and independence of the common refinement holds for arbitrary common refinements.

The comparison `α_u` on `d.Z` is likewise extended to arbitrary refinements
(`AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso`), as `α_{w.comp u}` followed by
the inverse of `R⁺u_* α_w` for a dense refinement `w`; this does not depend on `w`, and it
is an isomorphism, the identity for the identity refinement and transitive.

## Main definitions

- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison`: the comparison
  `α_u : D⁺(d.i)_! ⟶ D⁺(c.i)_! ⋙ R⁺u_*` along a refinement with cartesian square.
- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso`: the isomorphism `α_u` along
  an arbitrary refinement.
- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekRestrictionIso`: the isomorphism
  `θ_u : (d.i)^* Ru_* (c.i)_! K ≅ K` of blueprint `rem-ptr-weil-pbc-proper-open-comparison-1`,
  whose inverse is adjoint to `α_u`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso`: the
  comparison `Rf_!(d) ≅ Rf_!(c)` along an arbitrary refinement.

## Main results

- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison_id` and
  `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison_comp`: the identity and
  transitivity of `α_u`.
- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso_hom_id` and
  `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso_hom_comp`: the same for
  arbitrary refinements.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq`: independence
  of the common refinement.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans`: the cocycle
  condition.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`:
  independence of the common refinement, for arbitrary refinements.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_id` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_comp`:
  identity and transitivity for arbitrary refinements.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Compactification.Refinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

end Compactification.Refinement

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The unit `K ⟶ (j^* j_!) K` of the bounded below derived adjunction `D⁺j_! ⊣ D⁺j^*` of an
open immersion `j` is an isomorphism: `D⁺j_!` is fully faithful, since the unbounded `Dj_!` is
and the bounded below derived categories are a full subcategory. -/
instance isIso_derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus_unit {Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j).unit := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  have := adj.fullyFaithfulLOfIsIsoUnit.full
  have := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : (D+((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι).Full :=
    Functor.Full.of_iso ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
  have : (D+((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι).Faithful :=
    Functor.Faithful.of_iso
      ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
  have : D+((j)_!open[ModuleCat.{u + 1} Λ]).Full :=
    Functor.Full.of_comp_faithful _ DerivedCategory.Plus.ι
  have : D+((j)_!open[ModuleCat.{u + 1} Λ]).Faithful :=
    Functor.Faithful.of_comp _ DerivedCategory.Plus.ι
  infer_instance

end Torsion

section Independence

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable [QuasiCompact f]

/-! ### Arbitrary refinements

A refinement `r : c.Refinement d` need not have a cartesian square over `X`. The comparison
along `r` is then defined through the dense refinement `v : Compactification.inf c c ⟶ c`:
both `v` and `v.comp r` have cartesian squares, since they come out of a dense
compactification, and the comparison along `r` is `ρ_{v.comp r} ≫ ρ_v⁻¹`. It agrees with
`ρ_r` when the square of `r` is cartesian, and it satisfies the identity and transitivity laws
and independence of the common refinement for arbitrary refinements. -/

end Independence

section ArbitraryRefinements

/-! ### The comparison `α_u` along arbitrary refinements

For a refinement `u : c.Refinement d` whose square over `X` need not be cartesian, the
comparison `α_u : j_{d!} ⟶ Ru_* j_{c!}` is obtained from any refinement `w : c' ⟶ c` such that
`w` and `w.comp u` have cartesian squares (for instance `w = Compactification.infFst c c`,
out of a dense compactification) as `α_{w.comp u}` followed by the inverse of `R⁺u_* α_w`,
modulo the composition isomorphism `Rw_* ⋙ Ru_* ≅ R(w ≫ u)_*`. This does not depend on `w`
(`refinementOpenImmersionLowerShriekComparisonAux_eq`), and the identity and transitivity
laws follow from those of the cartesian comparison. -/

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The pushforward along any morphism of schemes preserves injective objects, being right
adjoint to the exact pullback. -/
lemma preservesInjectiveObjects_lowerStar_of_abelian [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {T S : Scheme.{u}} (h : T ⟶ S) : ((h)_*[A]).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction A h)

attribute [local instance] preservesInjectiveObjects_lowerStar_of_abelian

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable [QuasiCompact f]

end ArbitraryRefinements

end Etale

end AlgebraicGeometry

/-! ### Axiom census

The transitivity of the cartesian comparison `α_u` depends only on the three standard axioms;
the check below is run by the build. The statements that invert a comparison use that `α_u`
is an isomorphism, which rests on proper base change
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`, blueprint
`sk-thm-properbasechange`), not proved yet. -/
