/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BaseChangePasting

/-!
# Naturality, pasting and comparison of the pro-étale base change map

The three parts of blueprint `lemma-naturality-pasting-comparison`, for pro-étale sheaves of
`Λ`-modules, bundled into one statement
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap_naturality_paste_comparison`):

1. the base change maps are natural (`AlgebraicGeometry.ProEtale.derivedBaseChangeMap_naturality`);
2. they satisfy the identity and pasting laws
   (`AlgebraicGeometry.ProEtale.derivedBaseChangeMap_id_and_paste`);
3. for a cartesian square with `f`, `f'` qcqs, the comparison of the étale and pro-étale sites
   identifies the pro-étale base change map at `ν_X^* K` with the inverse image of the étale base
   change map at `K` (`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lemma-naturality-pasting-comparison`: **naturality, pasting and comparison** of the
pro-étale base change map for sheaves of `Λ`-modules. The maps `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` are
natural in `K`; they are the identity for an identity square and compatible with horizontal and
vertical pasting; and for a cartesian square with `f` and `f'` qcqs and `K ∈ D⁺(X_ét, Λ)`, the
comparison isomorphisms `α_K` and `β_K` identify the pro-étale base change map at `ν_X^* K` with
`ν_{Y'}^*` of the étale base change map at `K`. -/
theorem derivedBaseChangeMap_naturality_paste_comparison :
    (∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (sq : CommSq g' f' f g) {K K' : DerivedCategory (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} Λ))} (φ : K ⟶ K'),
      L((g)^*[ModuleCat.{u + 1} Λ]).map (R((f)_*[ModuleCat.{u + 1} Λ]).map φ) ≫
          (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K' =
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K ≫
          R((f')_*[ModuleCat.{u + 1} Λ]).map (L((g')^*[ModuleCat.{u + 1} Λ]).map φ)) ∧
    ((∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)),
      derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq =
        Functor.whiskerLeft R((f)_*[ModuleCat.{u + 1} Λ])
            (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).hom ≫
          (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv
            R((f)_*[ModuleCat.{u + 1} Λ])) ∧
    (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
      {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)),
      derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq =
        Functor.whiskerLeft R((f)_*[ModuleCat.{u + 1} Λ])
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h g).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₁)
            L((h)^*[ModuleCat.{u + 1} Λ]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L((g')^*[ModuleCat.{u + 1} Λ])
            (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g'' g').inv
            R((f'')_*[ModuleCat.{u + 1} Λ])) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k),
      derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq =
        Functor.whiskerRight (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) f e).inv
            L((k)^*[ModuleCat.{u + 1} Λ]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft R((f)_*[ModuleCat.{u + 1} Λ])
            (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₁)
            R((e')_*[ModuleCat.{u + 1} Λ]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L((g')^*[ModuleCat.{u + 1} Λ])
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) f' e').hom)) ∧
    (∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
      (sq : IsPullback g' f' f g)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
          (DerivedCategory.Plus.ι.map
            ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≫
        (baseChangeTargetComparisonIso g' f' Λ).hom.app K =
      (baseChangeSourceComparisonIso f g Λ).hom.app K ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj K))) :=
  ⟨fun sq _ _ φ ↦ derivedBaseChangeMap_naturality _ sq φ,
    derivedBaseChangeMap_id_and_paste _,
    fun sq K ↦ comparison_derivedBaseChangeMap Λ sq K⟩

end AlgebraicGeometry.ProEtale
