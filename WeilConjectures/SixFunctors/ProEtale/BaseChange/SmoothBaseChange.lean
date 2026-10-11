/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!
# Smooth base change on the pro-étale site, finite coefficients

Fix a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated, and a coefficient ring `Λ` killed by
a nonzero integer invertible on `S`. For a bounded constructible complex `K` of pro-étale
sheaves of `Λ`-modules on `T` (one of étale origin), the pro-étale exchange map
`p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism (blueprint
`sbc-thm-finite-proetale-smooth-base-change`). It is obtained by conjugating the étale exchange
isomorphism (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth`)
by the site comparison, as recorded by the transport lemma
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` of the proper base change
chapter.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (f) in
/-- Blueprint `prop-weil-pbc-comparison-direct-image`: for `f` quasi-compact and
quasi-separated, the canonical isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` on bounded below derived
categories, the base change morphism of right derived functors induced by the underived
comparison `ν_Y^* f_* ⟶ f_* ν_X^*`
(`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`). -/
noncomputable def rightDerivedLowerStarComparisonPlusIso [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ D+(ν^*(Y)[A]) ≅ D+(ν^*(X)[A]) ⋙ R+(ProEtale.lowerStar A f) :=
  have := isIso_lowerStarComparisonUpperStarBaseChange f A
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f A)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f A))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective A f I)
  asIso (Functor.rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange f A))

variable (f) in
/-- The isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` of
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso`, with the pro-étale direct
image the unbounded right derived functor, as functors `D⁺(X_ét) ⥤ D(Y_proét)`. -/
noncomputable def rightDerivedLowerStarComparisonIso' [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[A]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[A]) ⋙ R(ProEtale.lowerStar A f) :=
  Functor.isoWhiskerLeft R+(Etale.lowerStar A f)
      (ν^*(Y)[A]).mapDerivedCategoryPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarComparisonPlusIso f A) DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft D+(ν^*(X)[A])
      (ProEtale.lowerStar A f).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight (ν^*(X)[A]).mapDerivedCategoryPlusCompatibility
      R(ProEtale.lowerStar A f)

end Comparison

variable (Λ : Type (u + 1)) [CommRing Λ]

variable (g) in
/-- Blueprint `lem-weil-pbc-comparison-pullback`: the canonical isomorphism
`ν_{Y'}^* g^* ≅ Lg^* ν_Y^*`, as functors `D⁺(Y_ét) ⥤ D(Y'_proét)`. It is induced by the
underived isomorphism `AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`, the
derived pullback of the exact functor `g^*` being computed degreewise. -/
noncomputable def leftDerivedUpperStarComparisonIso :
    D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g) ⋙ DerivedCategory.Plus.ι ⋙
        D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g) :=
  Functor.isoWhiskerRight
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
      D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]))
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm

variable (f g) in
/-- The comparison `ν_{Y'}^* g^* Rf_* ≅ Lg^* Rf_* ν_X^*` of the sources of the étale and the
pro-étale exchange maps, as functors `D⁺(X_ét) ⥤ D(Y'_proét)`. -/
noncomputable def baseChangeSourceComparisonIso [QuasiCompact f] [QuasiSeparated f] :
    (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g)) ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g) :=
  Functor.isoWhiskerLeft R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
      (leftDerivedUpperStarComparisonIso g Λ) ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ))
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)

variable (g' f') in
/-- The comparison `ν_{Y'}^* Rf'_* g'^* ≅ Rf'_* Lg'^* ν_X^*` of the targets of the étale and the
pro-étale exchange maps, as functors `D⁺(X_ét) ⥤ D(Y'_proét)`. -/
noncomputable def baseChangeTargetComparisonIso [QuasiCompact f'] [QuasiSeparated f'] :
    (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g') ⋙ R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f')) ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g') ⋙
          R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f') :=
  Functor.isoWhiskerLeft D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g')
      (rightDerivedLowerStarComparisonIso' f' (ModuleCat.{u + 1} Λ)) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComparisonIso g' Λ)
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f')

/-- Blueprint `lem-weil-pbc-transport-identifies-exchange` (subsection
`sk-thm-properbasechange`): for a Cartesian square

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

with `f` (hence `f'`) quasi-compact and quasi-separated, and `L ∈ D⁺(X_ét, Λ)`, conjugating
the étale exchange map `g^* Rf_* L ⟶ Rf'_* g'^* L` by the comparison isomorphisms
`ν_{Y'}^* g^* Rf_* L ≅ Lg^* Rf_* ν_X^* L` and `ν_{Y'}^* Rf'_* g'^* L ≅ Rf'_* Lg'^* ν_X^* L`
(`AlgebraicGeometry.ProEtale.baseChangeSourceComparisonIso`,
`AlgebraicGeometry.ProEtale.baseChangeTargetComparisonIso`) gives the pro-étale exchange map
at `ν_X^* L`. -/
theorem comparison_derivedBaseChangeMap [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
    [QuasiSeparated f'] (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
        (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫
      (baseChangeTargetComparisonIso g' f' Λ).hom.app L =
    (baseChangeSourceComparisonIso f g Λ).hom.app L ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj L)) :=
  sorry

end ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (p) in
/-- Blueprint `sbc-thm-finite-proetale-smooth-base-change`: for a Cartesian square with `p`
smooth and `g` quasi-compact and quasi-separated, and a coefficient ring `Λ` killed by a
nonzero integer `N` invertible on `S`, the pro-étale exchange map
`p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism for every bounded constructible pro-étale complex
`K` (that is, of étale origin). -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p) (N : ℕ) (hN₀ : N ≠ 0) (hN : (N : Λ) = 0)
    (hNS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hK : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hK
  let L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨K', hK'.1.1⟩
  let eK' : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K := eK
  rw [← NatTrans.isIso_app_iff_of_iso _ eK']
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) :=
    Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth Λ p sq N hN₀ hN hNS K' hK'
  have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated h :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso g p Λ).app L)
      ((ProEtale.baseChangeTargetComparisonIso e h Λ).app L) hαβ.symm)).1 this

variable (p) in
/-- The pro-étale exchange map `p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism, for `p` smooth and
`g` quasi-compact and quasi-separated, at every complex `K = ν^* L` of étale origin with `L` a
bounded below complex of étale sheaves of `Λ`-modules whose cohomology sheaves are torsion of
orders invertible on `S`. The coefficient ring `Λ` is arbitrary (for instance `Λ = 𝒪_E` and `L`
killed by a power of a uniformizer): the torsion condition is imposed on the cohomology sheaves
instead (compare `AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`). -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_smooth_of_torsionHomology [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ T S.invertiblePrimes L) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj L))) := by
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) :=
    Etale.isIso_baseChange_app_of_smooth Λ p sq L hL
  have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated h :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso g p Λ).app L)
      ((ProEtale.baseChangeTargetComparisonIso e h Λ).app L) hαβ.symm)).1 this

end AlgebraicGeometry
