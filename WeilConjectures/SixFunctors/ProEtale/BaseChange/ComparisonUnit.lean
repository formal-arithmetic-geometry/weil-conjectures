/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnitComplex

/-!
# The site comparison and the units of the direct image adjunctions

Let `f : U ⟶ V` be a quasi-compact quasi-separated morphism of schemes and `ν^*` the comparison
from the étale to the pro-étale site. On bounded below complexes, `ν^*` commutes with the derived
pullbacks (`ProEtale.leftDerivedUpperStarComparisonIso`) and with the derived direct images
(`ProEtale.rightDerivedLowerStarComparisonIso'`), compatibly with the counits of the adjunctions
`f^* ⊣ Rf_*` (`ProEtale.ComparisonCore.comparison_counit`). Hence the two comparisons are also
compatible with the units (`ProEtale.comparison_unit`): `ν^*` of the étale unit
`G ⟶ Rf_* f^* G`, followed by the comparisons, is the pro-étale unit at `ν^* G`.

As an application, the pro-étale nearby cycles of a constant complex on a strictly henselian local
ring are trivial: for a strictly henselian local ring `R`, a morphism `t : Spec Ω ⟶ Spec R` from
the spectrum of a separably closed field, a map `b : R ⟶ κ` to a field with kernel the maximal
ideal and a bounded below complex `G` of étale sheaves on `Spec R` with constant cohomology
sheaves, the pullback along `Spec b` of the pro-étale unit `ν^* G ⟶ Rt_* Lt^* ν^* G` is an
isomorphism (`ProEtale.isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology`). This is
the étale statement
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_app_of_isConstant_homology`) transported along
`ν^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The site comparison and the units**: for a quasi-compact quasi-separated `f : U ⟶ V` and
`G ∈ D⁺(V_ét)`, `ν^*` of the étale unit `G ⟶ Rf_* f^* G`, followed by the comparisons
`ν^* Rf_* ≅ Rf_* ν^*` and `ν^* f^* ≅ Lf^* ν^*`, is the pro-étale unit
`ν^* G ⟶ Rf_* Lf^* ν^* G`. -/
theorem comparison_unit {U V : Scheme.{u}} (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f]
    (G : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ])).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app G) ≫
      (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map
        ((leftDerivedUpperStarComparisonIso f Λ).hom.app G) =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ])).obj G) :=
  sorry

/-- **Pro-étale nearby cycles of constant complexes over a strictly henselian local ring**: let
`R` be a strictly henselian local ring, `t : Spec Ω ⟶ Spec R` a morphism from the spectrum of a
separably closed field and `b : R ⟶ κ` a map to a field with kernel the maximal ideal. For a
bounded below complex `G` of étale sheaves of `Λ`-modules on `Spec R` with constant cohomology
sheaves, the pullback along `Spec b` of the pro-étale unit `ν^* G ⟶ Rt_* Lt^* ν^* G` is an
isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
    {κ : Type u} [Field κ] (b : R →+* κ) (hb : RingHom.ker b = IsLocalRing.maximalIdeal R)
    (G : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : ∀ q, Sheaf.IsConstant (Spec (.of R)).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ q).obj G)) :
    IsIso (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (Spec.map (CommRingCat.ofHom b))).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Spec (.of R))[ModuleCat.{u + 1} Λ])).obj G))) :=
  sorry

end AlgebraicGeometry.ProEtale
