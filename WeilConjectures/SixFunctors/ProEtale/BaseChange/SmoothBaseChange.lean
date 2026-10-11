/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible

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
`AlgebraicGeometry.ProEtale.exists_comparison_derivedBaseChangeMap` of the proper base change
chapter.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `lem-weil-pbc-transport-identifies-exchange` (subsection
`sk-thm-properbasechange`): for a Cartesian square

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

and `L ∈ D⁺(X_ét, Λ)`, conjugating the étale exchange map `g^* Rf_* L ⟶ Rf'_* g'^* L` by
comparison isomorphisms `ν^* g^* Rf_* L ≅ g^* Rf_* ν^* L` and `ν^* Rf'_* g'^* L ≅ Rf'_* g'^* ν^* L`
gives the pro-étale exchange map at `ν^* L`. -/
theorem ProEtale.exists_comparison_derivedBaseChangeMap (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (α : (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
            (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).obj L)) ≅
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
          (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))
      (β : (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          (((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
            (Etale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctorPlus).obj L)) ≅
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
          (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L))),
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫ β.hom =
        α.hom ≫ (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)) :=
  sorry

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
  obtain ⟨α, β, hαβ⟩ := ProEtale.exists_comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (Arrow.isoMk α β hαβ.symm)).1 this

end AlgebraicGeometry
