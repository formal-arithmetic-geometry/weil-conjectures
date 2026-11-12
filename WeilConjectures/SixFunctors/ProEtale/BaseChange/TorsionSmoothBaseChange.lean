/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Pro-étale smooth base change for complexes killed by an integer invertible on the base

This file extends the finite-coefficient pro-étale smooth base change
`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth` (blueprint
`sbc-thm-finite-proetale-smooth-base-change`) from coefficient rings killed by an integer `N`
invertible on the base to complexes killed by such an integer, over an arbitrary coefficient ring
`Λ`. This is the form needed at the finite levels of the adic theorem, where the coefficient ring
is `𝒪_E` and the reductions `K ⊗ᴸ 𝒪_E/𝔪ⁿ` are killed by `ℓⁿ`.

Fix a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth_of_torsion`: the
  pro-étale exchange map `p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism at `K ≅ ν^* L` for a bounded
  below étale complex `L` whose cohomology sheaves are torsion of orders invertible on `S`.
- `AlgebraicGeometry.ProEtale.isIso_homologyFunctor_map_derivedBaseChangeMap_app_of_smooth`: the
  degree-`q` base change map `p^* R^q g_* F ⟶ R^q h_* e^* F` is an isomorphism for a classical
  pro-étale sheaf `F ≅ ν^* G` with `G` torsion of orders invertible on `S` (blueprint
  `theorem-smooth-base-change-classical-torsion`).
- `AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth_of_nsmul_eq_zero`: it is an
  isomorphism at every bounded constructible pro-étale complex (one of étale origin) killed by an
  integer invertible on `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A sheaf of `Λ`-modules on the small étale site of `T` killed by a positive integer `N`
invertible on `S` is torsion of orders invertible on `S`. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero {S T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {N : ℕ} (hN₀ : N ≠ 0)
    (hNS : IsUnit (N : Γ(S, ⊤))) (hN : N • 𝟙 F = 0) : IsTorsionSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
      (pointSmallEtale s).sheafFiber_additive
    have h : N • 𝟙 ((pointSmallEtale s).sheafFiber.obj F) = 0 := by
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hN, Functor.map_zero]
    refine ⟨N, Nat.pos_of_ne_zero hN₀, hNS, ?_⟩
    have := congrArg (fun φ ↦ φ.hom x) h
    simpa using this

namespace ProEtale

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (Λ) in
/-- The pro-étale exchange map `p^* Rg_* K ⟶ Rh_* e^* K` of a Cartesian square with `g`
quasi-compact and quasi-separated is an isomorphism at `K ≅ ν^* L`, for a bounded below étale
complex `L` at which the étale exchange map `p⁻¹ Rg_* L ⟶ Rh_* e⁻¹ L` is an isomorphism: the
two exchange maps correspond under the site comparison
(`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`). -/
theorem isIso_derivedBaseChangeMap_app_of_isIso_baseChange_app [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p)
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (eK : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ eK]
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

variable (Λ p) in
/-- The pro-étale exchange map `p^* Rg_* K ⟶ Rh_* e^* K` of a Cartesian square with `p` smooth
and `g` quasi-compact and quasi-separated is an isomorphism at `K ≅ ν^* L`, for a bounded below
étale complex `L` whose cohomology sheaves are torsion of orders invertible on `S`. As for
`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`, this is the étale smooth
base change
(`AlgebraicGeometry.Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder`)
transported along the site comparison. -/
theorem isIso_derivedBaseChangeMap_app_of_smooth_of_torsion [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p)
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : ∀ j, IsTorsionSheafOfInvertibleOrder S
      ((DerivedCategory.Plus.homologyFunctor _ j).obj L))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (eK : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  isIso_derivedBaseChangeMap_app_of_isIso_baseChange_app Λ sq L
    (Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ p sq L hL) K eK

variable (Λ p) in
/-- Blueprint `theorem-smooth-base-change-classical-torsion`: smooth base change for classical
torsion sheaves. For a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated, let `F` be a classical pro-étale sheaf
of `Λ`-modules on `T`, that is `F ≅ ν^* G` for a sheaf `G` on `T_ét`, with `G` torsion of orders
invertible on `S` (equivalently, `G` is the filtered union of its subsheaves `G[n]` for the
positive integers `n` invertible on `S`). Then for every `q` the degree-`q` base change map
`p^* R^q g_* F ⟶ R^q h_* e^* F`, the degree-`q` cohomology of the pro-étale exchange map (4.5) at
`F` placed in degree `0`, is an isomorphism. Abelian sheaves are the case `Λ = ℤ`.

The pro-étale map is the étale one transported along the site comparison
(`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isIso_baseChange_app`), and the
étale map is an isomorphism by the étale smooth base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`. -/
theorem isIso_homologyFunctor_map_derivedBaseChangeMap_app_of_smooth [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionSheafOfInvertibleOrder S G]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))
    (eF : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj G ≅ F) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  let ν := comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  have := isIso_derivedBaseChangeMap_app_of_isIso_baseChange_app Λ sq
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
    (Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth Λ p sq G)
    ((DerivedCategory.singleFunctor _ 0).obj F)
    (ν.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
      (ν.mapDerivedCategorySingleFunctor 0).app G ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eF)
  infer_instance

variable (Λ p) in
/-- The pro-étale exchange map `p^* Rg_* K ⟶ Rh_* e^* K` of a Cartesian square with `p` smooth
and `g` quasi-compact and quasi-separated is an isomorphism at every bounded constructible
pro-étale complex `K` of `Λ`-modules (one of étale origin) killed by a nonzero integer `N`
invertible on `S`. The étale complex `L` with `ν^* L ≅ K` is then also killed by `N`, `ν^*` being
faithful on bounded below complexes, so that its cohomology sheaves are torsion of orders
invertible on `S`. -/
theorem isIso_derivedBaseChangeMap_app_of_smooth_of_nsmul_eq_zero [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p) {N : ℕ} (hN₀ : N ≠ 0)
    (hNS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hK : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K)
    (hNK : N • 𝟙 K = 0) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hK
  let L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨K', hK'.1.1⟩
  have hK'N : N • 𝟙 K' = 0 := by
    apply (bijective_comparisonUpperStar_mapDerivedCategory_map K' K' hK'.1.1).1
    dsimp only
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
    rw [← cancel_mono eK.hom, Preadditive.nsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id eK.hom, ← Preadditive.comp_nsmul, hNK, Limits.comp_zero]
  have hL : ∀ j, IsTorsionSheafOfInvertibleOrder S
      ((DerivedCategory.Plus.homologyFunctor _ j).obj L) := fun j ↦
    IsTorsionSheafOfInvertibleOrder.of_nsmul_id_eq_zero _ hN₀ hNS (by
      change N • 𝟙 ((_root_.DerivedCategory.homologyFunctor _ j).obj K') = 0
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hK'N, Functor.map_zero])
  exact isIso_derivedBaseChangeMap_app_of_smooth_of_torsion Λ p sq L hL K eK

end ProEtale

end AlgebraicGeometry
