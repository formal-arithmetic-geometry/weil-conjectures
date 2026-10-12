/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Transport

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

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

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
