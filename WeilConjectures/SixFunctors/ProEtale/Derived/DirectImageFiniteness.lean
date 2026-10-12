/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Bounded
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Derived.ConstructibleSerre

/-!
# Direct-image finiteness and bounded constructible pro-étale complexes

Let `Λ` be a finite commutative ring (a finite level `P_n = A/Iⁿ` of an adic coefficient datum).
A sheaf of `Λ`-modules on the small pro-étale site is *constructible* if it is `ν^* F'` for a
constructible étale sheaf `F'` (`AlgebraicGeometry.ProEtale.constructibleSheaf`).

## Main definitions

- `AlgebraicGeometry.ProEtale.DirectImageFiniteness Λ f c`, the condition `FIN(f, Λ; c)` of
  blueprint `def-weil-pbc-constructible-direct-image-finiteness`: the higher direct images
  `Rᵠf_* F` of constructible pro-étale sheaves are constructible, and vanish for `q > c`.

## Main results

- `AlgebraicGeometry.ProEtale.DirectImageFiniteness.boundedConstructible_rightDerivedLowerStar`
  and the functor `DirectImageFiniteness.rightDerivedLowerStarBoundedConstructible`
  (blueprint `prop-weil-pbc-restriction-direct-image`): under `FIN(f, Λ; c)`, `Rf_*` restricts
  to a triangulated functor `Dᵇc_proét(S, Λ) ⥤ Dᵇc_proét(T, Λ)`, sending complexes with
  cohomology in `[a, b]` to complexes with cohomology in `[a, b + c]`.
- `AlgebraicGeometry.ProEtale.boundedConstructible_leftDerivedUpperStar` and the functor
  `AlgebraicGeometry.ProEtale.upperStarBoundedConstructible` (blueprint
  `lem-weil-pbc-pullback-preserves-bounded-constructible`): `Lg^*` restricts to a triangulated
  functor `Dᵇc_proét(V, Λ) ⥤ Dᵇc_proét(V', Λ)` preserving the cohomological interval.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `def-weil-pbc-constructible-direct-image-finiteness`: the constructible
direct-image finiteness condition `FIN(f, Λ; c)`.

For a morphism `f : S ⟶ T`, `FIN(f, Λ; c)` holds if for every constructible sheaf `F` of
`Λ`-modules on `S_proét` (`AlgebraicGeometry.ProEtale.constructibleSheaf`):
1. *constructibility of direct images:* every `Rᵠf_* F` is constructible on `T_proét`;
2. *amplitude:* `Rᵠf_* F = 0` for `q > c`.

The sheaves `Rᵠf_* F` are the classical right derived functors of the pro-étale direct image
`f_*`. The standing assumptions of the blueprint (`T` noetherian of finite dimension, the
order of `Λ` invertible on `T`) are hypotheses of the results using this condition. -/
structure DirectImageFiniteness {S T : Scheme.{u}} (f : S ⟶ T) (c : ℕ) : Prop where
  constructibleSheaf_rightDerived_obj
    (F : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ)) (hF : constructibleSheaf Λ S F)
    (q : ℕ) :
    constructibleSheaf Λ T (((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q).obj F)
  isZero_rightDerived_obj
    (F : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ)) (hF : constructibleSheaf Λ S F)
    (q : ℕ) (hq : c < q) :
    IsZero (((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q).obj F)

variable {Λ} [Finite Λ]

section DirectImage

variable {S T : Scheme.{u}} {f : S ⟶ T} {c : ℕ}

/-- Blueprint `prop-weil-pbc-restriction-direct-image`: Restriction of the direct image to
bounded constructibles, objectwise.

Under `FIN(f, Λ; c)`, if `K ∈ Dᵇc_proét(S, Λ)` has cohomology in `[a, b]`, then
`Rf_* K ∈ Dᵇc_proét(T, Λ)` and has cohomology in `[a, b + c]`. The blueprint's spectral sequence
argument is the dévissage `CategoryTheory.Functor.rightDerivedFunctor_obj_homologyProperty`
along the truncation triangles, using that constructible pro-étale sheaves form a weak Serre
subcategory (`thm-constructible-serre`). -/
theorem DirectImageFiniteness.boundedConstructible_rightDerivedLowerStar
    (h : DirectImageFiniteness Λ f c) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S K)
    (hab : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
      _root_.DerivedCategory.homologyConcentratedIn a (b + c)
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨h₁, h₂⟩ :=
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor_obj_homologyProperty
      (constructibleSheaf Λ S) (constructibleSheaf Λ T) c h.constructibleSheaf_rightDerived_obj
      h.isZero_rightDerived_obj a b K hab hK.homologyProperty
  obtain ⟨h₂₁, h₂₂⟩ := h₂
  exact ⟨(DerivedCategory.boundedConstructible_iff_homologyProperty _).2
    ⟨⟨⟨a, h₂₁⟩, ⟨b + c, h₂₂⟩⟩, h₁⟩, h₂₁, h₂₂⟩

/-- Under `FIN(f, Λ; c)`, `Rf_*` sends bounded constructible pro-étale complexes to bounded
constructible ones. -/
theorem DirectImageFiniteness.boundedConstructible_rightDerivedLowerStar_obj
    (h : DirectImageFiniteness Λ f c)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.bounded
  exact (h.boundedConstructible_rightDerivedLowerStar hK ⟨ha, hb⟩).1

/-- Blueprint `prop-weil-pbc-restriction-direct-image`: Restriction of the direct image to
bounded constructibles.

Under `FIN(f, Λ; c)`, the derived direct image `Rf_*` restricts to a functor
`Dᵇc_proét(S, Λ) ⥤ Dᵇc_proét(T, Λ)`; it is triangulated (the instances on
`CategoryTheory.ObjectProperty.lift`), and sends complexes with cohomology in `[a, b]` to
complexes with cohomology in `[a, b + c]`
(`AlgebraicGeometry.ProEtale.DirectImageFiniteness.boundedConstructible_rightDerivedLowerStar`). -/
noncomputable abbrev DirectImageFiniteness.rightDerivedLowerStarBoundedConstructible
    (h : DirectImageFiniteness Λ f c) :
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S).FullSubcategory ⥤
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T).FullSubcategory :=
  (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T).lift
    ((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S).ι ⋙
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f))
    fun K ↦ h.boundedConstructible_rightDerivedLowerStar_obj K.2

example (h : DirectImageFiniteness Λ f c) :
    h.rightDerivedLowerStarBoundedConstructible.IsTriangulated := inferInstance

end DirectImage

section Pullback

variable {V V' : Scheme.{u}} (g : V' ⟶ V)

/-- `Lg^* (ν^* K') ≅ ν^* (g^* K')` for a bounded below étale complex `K'`: the comparison
pullback isomorphism (`lem-weil-pbc-comparison-pullback`) followed by the computation of the
étale `D⁺(g^*)` degreewise. -/
noncomputable def leftDerivedUpperStarMapDerivedCategoryObjIso
    (K' : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK' : _root_.DerivedCategory.TStructure.t.plus K') :
    (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)).obj (D(ν^*(V)[ModuleCat.{u + 1} Λ]).obj K') ≅
      D(ν^*(V')[ModuleCat.{u + 1} Λ]).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.obj K') :=
  ((leftDerivedUpperStarComparisonIso g Λ).app ⟨K', hK'⟩).symm ≪≫
    D(ν^*(V')[ModuleCat.{u + 1} Λ]).mapIso
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility).app
        ⟨K', hK'⟩)

omit [Finite Λ] in
/-- Blueprint `lem-weil-pbc-pullback-preserves-bounded-constructible`: Pullback preserves
bounded constructibility, objectwise.

The derived pullback `Lg^*` sends `Dᵇc_proét(V, Λ)` into `Dᵇc_proét(V', Λ)`, and preserves the
cohomological interval `[a, b]`. Writing `K ≅ ν^* K'`, `Lg^* K ≅ ν^* (g^* K')`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarMapDerivedCategoryObjIso`), and `g^* K'` is
bounded constructible on the étale site
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar`);
the interval is preserved since `Lg^* ≅ D(g^*)` for the exact functor `g^*`. -/
theorem boundedConstructible_leftDerivedUpperStar
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V'
      ((L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  exact (DerivedCategory.boundedConstructible _ V').prop_of_iso
    ((leftDerivedUpperStarMapDerivedCategoryObjIso g K' hK'.1.1).symm ≪≫
      (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)).mapIso e)
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      (hK'.mapDerivedCategory_upperStar g))

omit [Finite Λ] in
/-- Blueprint `lem-weil-pbc-pullback-preserves-bounded-constructible`: `Lg^*` preserves
cohomology concentrated in `[a, b]`, being isomorphic to `D(g^*)` for the exact functor
`g^*`. -/
theorem homologyConcentratedIn_leftDerivedUpperStar {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a b
      ((L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)).obj K) :=
  (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).app K).symm
    ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).homologyConcentratedIn_mapDerivedCategory_obj
      hK)

/-- Blueprint `lem-weil-pbc-pullback-preserves-bounded-constructible`: Pullback preserves
bounded constructibility.

The pullback `Lg^* = g^{-1}`, realised as the derived functor `D(g^*)` of the exact functor `g^*`
(isomorphic to `Lg^*`, `AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`),
restricts to a functor `Dᵇc_proét(V, Λ) ⥤ Dᵇc_proét(V', Λ)`; it is triangulated (the instances
on `CategoryTheory.ObjectProperty.lift`), and preserves the cohomological interval
(`AlgebraicGeometry.ProEtale.homologyConcentratedIn_leftDerivedUpperStar`). -/
noncomputable abbrev upperStarBoundedConstructible :
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).FullSubcategory ⥤
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V').FullSubcategory :=
  (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V').lift
    ((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V).ι ⋙
      D(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g))
    fun K ↦ (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V').prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).app K.1)
      (boundedConstructible_leftDerivedUpperStar g K.2)

example : (upperStarBoundedConstructible (Λ := Λ) g).IsTriangulated := inferInstance

end Pullback

end AlgebraicGeometry.ProEtale
