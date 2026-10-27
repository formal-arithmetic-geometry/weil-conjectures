/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit
import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare

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

section
variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {l' : E₂ ⥤ E₃} {r' : E₃ ⥤ E₂}
  {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} {p' : P₂ ⥤ P₃} {s' : P₃ ⥤ P₂}
  (e : l ⊣ r) (e' : l' ⊣ r') (d : p ⊣ s) (d' : p' ⊣ s')
  {g : E₀ ⥤ E₂} {h : E₁ ⥤ E₃} {q : P₀ ⥤ P₂} {t : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}
  (a : l ⋙ A₁ ≅ A₀ ⋙ p) (a' : l' ⋙ A₃ ≅ A₂ ⋙ p')
  (c : g ⋙ A₂ ≅ A₀ ⋙ q) (c' : h ⋙ A₃ ≅ A₁ ⋙ t)
  (b : r ⋙ A₀ ⟶ A₁ ⋙ s) (b' : r' ⋙ A₂ ⟶ A₃ ⋙ s')
  (θ : g ⋙ l' ⟶ l ⋙ h) (ϑ : q ⋙ p' ⟶ p ⋙ t)
  (hb : ∀ K, a.hom.app (r.obj K) ≫ p.map (b.app K) ≫ d.counit.app (A₁.obj K) =
    A₁.map (e.counit.app K))
  (hb' : ∀ K, a'.hom.app (r'.obj K) ≫ p'.map (b'.app K) ≫ d'.counit.app (A₃.obj K) =
    A₃.map (e'.counit.app K))
  (hsq : ∀ M, A₃.map (θ.app M) ≫ c'.hom.app (l.obj M) ≫ t.map (a.hom.app M) =
    a'.hom.app (g.obj M) ≫ p'.map (c.hom.app M) ≫ ϑ.app (A₀.obj M))

include a a' hb hb' hsq in
private theorem comparison_mate_transport (K : E₁) :
    A₂.map ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K) ≫ b'.app (h.obj K) ≫
      s'.map (c'.hom.app K) =
    c.hom.app (r.obj K) ≫ q.map (b.app K) ≫
      (mateEquiv d d' (TwoSquare.mk _ _ _ _ ϑ)).natTrans.app (A₁.obj K) := by
  apply (d'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a'.hom.app (g.obj (r.obj K)))).1
  have hn := a'.hom.naturality ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [d'.counit_naturality, reassoc_of% hb']
  rw [← A₃.map_comp_assoc, mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := c'.hom.naturality (e.counit.app K)
  simp only [Functor.comp_map] at hn'
  erw [hn', mateEquiv_counit]
  have ht := ϑ.naturality (b.app K)
  simp only [Functor.comp_map] at ht
  erw [reassoc_of% ht, ← reassoc_of% hsq]
  simp only [← Functor.map_comp, hb, TwoSquare.mk, Functor.comp_obj]

end

namespace AlgebraicGeometry

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

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
        ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj L)) := by
  have h := comparison_mate_transport
    (A₀ := DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]))
    (A₁ := DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]))
    (A₂ := DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]))
    (A₃ := DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ]))
    (g := D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g))
    (h := D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g'))
    (q := L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g))
    (t := L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g'))
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f')
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (leftDerivedUpperStarComparisonIso f Λ)
    (leftDerivedUpperStarComparisonIso f' Λ)
    (leftDerivedUpperStarComparisonIso g Λ)
    (leftDerivedUpperStarComparisonIso g' Λ)
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom
    (rightDerivedLowerStarComparisonIso' f' (ModuleCat.{u + 1} Λ)).hom
    (Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (comparison_counit Λ f) (comparison_counit Λ f') (comparison_square Λ sq) L
  simpa [baseChangeSourceComparisonIso, baseChangeTargetComparisonIso,
    derivedBaseChangeMap, Etale.baseChange_app, Etale.baseChangeUnitStep_app,
    Etale.baseChangeSquareStep_hom_app, Etale.baseChangeCounitStep_app,
    mateEquiv_apply, TwoSquare.natTrans, TwoSquare.mk, Category.assoc] using h

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

end AlgebraicGeometry
