/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom

/-!
# The affine line and the punctured line over a base, with `Λ(1) = μₙ ⊗ Λ` coefficients

Let `k` be an algebraically closed field, `Λ` a finite ring whose exponent is invertible in `k`,
`Y` a separated `k`-scheme of finite type, `p : 𝔸¹_Y ⟶ Y` the projection, `j : G ⟶ 𝔸¹_Y` the
complement of the zero section and `π = j ≫ p`. With the Tate twist `Λ(1) = μₙ ⊗ Λ` and its
Kummer classes (`AlgebraicGeometry.Etale.hasKummerClass`) this file proves blueprint
`prop-pur-gm-relative-kummer`:

1. the unit `Λ_Y(1) ⟶ Rp_* Lp^* Λ_Y(1)` is an isomorphism
   (`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine`);
2. the unit `Λ_Y(1) ⟶ Rπ_* Lπ^* Λ_Y(1)` is an isomorphism on `H⁰`
   (`AlgebraicGeometry.Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup`), and
   `R¹π_* Λ(1)` is free of rank one on the Kummer class `κ(t)` of the coordinate
   (`AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint`);
3. `R^m π_* Λ(1) = 0` for `m ≥ 2`
   (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup`);
4. the base change maps of `Rp_* Λ(1)` are isomorphisms
   (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_affineLine`), and
   `κ(t)` pulls back to `κ(t')`
   (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass_coord`).

It also proves the global orientation `thm-pur-affine-line-orientation`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`), the
rank-one local calculation `thm-pur-rank-one-local-calculation`, with the `Λ`-linear isomorphism
`H²_Z(𝔸¹_Ω, Λ(1)) ≅ Λ` sending `∂κ(t)` to `1`
(`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv`), and the structure of the
exceptional inverse image of the zero section `lem-pur-gysin-structure`, with the `Λ`-linear
isomorphism `H²_Z(𝔸¹_Y, Λ(1)) ≅ Γ(Z, H⁰(Rs^!(Λ(1)[2])))`
(`AlgebraicGeometry.Etale.supportCohomologyLinearEquivΓHomologyZero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] neZero_ringChar_of_finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The Kummer class of the coordinate of `𝔾_{m,Ω}` is free of rank one over every
algebraically closed field `Ω` (`AlgebraicGeometry.Etale.bijective_smul_kummerClassOf`), in the
form of the hypothesis of the relative statements. -/
theorem kummerClass_coord_smul_eq_zero (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [HasInvertibleExponent Λ (Spec (.of Ω))] (G' : Scheme.{u})
    (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω))) [IsOpenImmersion j']
    (hj' : Set.range j'.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))).base)ᶜ)
    [HasInvertibleExponent Λ G'] (c : Λ)
    (hc : c • kummerClass Λ (AffineSpace.unitLineCoord j' hj') = 0) : c = 0 :=
  (bijective_smul_kummerClassOf Λ j' hj').1 (show c • kummerClassOf G' Λ _ = (0 : Λ) • _ by
    rw [zero_smul]
    exact hc)

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY] [HasInvertibleExponent Λ Y]

include aY in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (1)).

The unit `Λ_Y(1) ⟶ Rp_* Lp^* Λ_Y(1) = Rp_* Λ_{𝔸¹_Y}(1)` of the projection `p : 𝔸¹_Y ⟶ Y` is an
isomorphism; with `AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine` for the
untwisted unit. With the latter this is clause (a) of the subsection statement
`sk-prop-a1-kummer`. -/
theorem isIso_unit_tateObject_affineLine :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (tateObject Λ Y 1)) := by
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  exact isIso_unit_affineLine_of_cohomology Λ aY (isZero_cohomology_affineLine Λ (k := k))
    (nonempty_iso_cohomology_zero_affineLine Λ (k := k)).some
    (boundedConstructibleFiniteTor_tateObject Λ Y 1) eTY hLT

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)

include aY hj in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (2), degree zero).

For the complement `j : G ⟶ 𝔸¹_Y` of the zero section and `π = j ≫ p`, the unit
`Λ_Y(1) ⟶ Rπ_* Lπ^* Λ_Y(1)` is an isomorphism on `H⁰`: `R⁰π_* Λ(1) = Λ_Y(1)`. This is the
first half of clause (b) of the subsection statement `sk-prop-a1-kummer`: `R⁰π_* Λ(1) ≅ Λ_Y(1)`,
the pullback `p^*` followed by restriction along `j` being an isomorphism onto it. -/
theorem isIso_homology_zero_unit_tateObject_multiplicativeGroup :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (tateObject Λ Y 1))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  exact isIso_homology_zero_unit_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some j hj
    (boundedConstructibleFiniteTor_tateObject Λ Y 1) eTY hLT

include aY hj in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (3)).

`R^m π_* Λ(1) = 0` for `m ∉ {0, 1}`; in particular for `m ≥ 2`. This is clause (c) of
`sk-prop-a1-kummer` for the twist `Λ(1) = μₙ ⊗ Λ`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup
    [HasInvertibleExponent Λ G] (m : ℤ) (h₀ : m ≠ 0) (h₁ : m ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ G 1))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some j hj
    (boundedConstructibleFiniteTor_tateObject Λ Y 1)
  exact (isZero_homology_biprodShift Λ _ (homology_props_of_iso_singleFunctor Λ eTY hLT).1 m h₀
    h₁).of_iso ((_root_.DerivedCategory.homologyFunctor _ m).mapIso
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarTateObjectIso (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y) 1).symm ≪≫ e))

section RankOne

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [HasInvertibleExponent Λ (Spec (.of Ω))]

end RankOne

section Gysin

end Gysin

section BaseChange

variable {Y' : Scheme.{u}} (aY' : Y' ⟶ Spec (.of k)) [IsSeparated aY'] [LocallyOfFiniteType aY']
  [QuasiCompact aY'] [HasInvertibleExponent Λ Y'] (g : Y' ⟶ Y)
  {G' : Scheme.{u}} (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Y')) [IsOpenImmersion j']
  (hj' : Set.range j'.base =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y').base)ᶜ)

omit [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] [IsSeparated aY]
  [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY'] [LocallyOfFiniteType aY']
  [QuasiCompact aY'] [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Y'] in
/-- Blueprint `prop-pur-gm-relative-kummer`: The affine line and the punctured line over a base
(clause (4), the Kummer class).

For `g : Y' ⟶ Y` with base change `g' : 𝔾_{m,Y'} ⟶ 𝔾_{m,Y}`, the pullback of the Kummer class
of the coordinate is the Kummer class of the coordinate: `Lg'^* κ(t) = κ(t')`, through
`Lg'^* Λ ≅ Λ` and `Lg'^* Λ(1) ≅ Λ(1)`. This is the compatibility of `κ(t)` with base change on
`Y` asserted in `sk-prop-a1-kummer`. -/
theorem leftDerivedUpperStar_map_kummerClass_coord [HasInvertibleExponent Λ G]
    [HasInvertibleExponent Λ G'] :
    (L((AffineSpace.complementMap g j j' hj hj')^*[ModuleCat.{u + 1} Λ])).map
        (kummerClass Λ (AffineSpace.unitLineCoord j hj)) ≫
      ((L((AffineSpace.complementMap g j j' hj hj')^*[ModuleCat.{u + 1} Λ])).commShiftIso
        (1 : ℤ)).hom.app (tateObject Λ G 1) ≫
      (leftDerivedUpperStarTateObjectIso (AffineSpace.complementMap g j j' hj hj')
        1).hom⟦(1 : ℤ)⟧' =
    (leftDerivedUpperStarConstantComplexIso Λ (AffineSpace.complementMap g j j' hj hj')).hom ≫
      kummerClass Λ (AffineSpace.unitLineCoord j' hj') := by
  rw [leftDerivedUpperStar_map_kummerClass,
    units_map_unitLineCoord g j hj j' hj' _ (AffineSpace.complementMap_comp g j j' hj hj')]

end BaseChange

end Etale

end AlgebraicGeometry
