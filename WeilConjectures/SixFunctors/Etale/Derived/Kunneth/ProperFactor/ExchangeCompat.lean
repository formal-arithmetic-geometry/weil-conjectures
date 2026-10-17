/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# The Künneth map and the exchange map of an open immersion

Let `j : U ⟶ X` be a morphism of `S`-schemes, `Y` an `S`-scheme, `W = X ×_S Y` with projections
`q : W ⟶ X`, `r : W ⟶ Y`, and `V = U ×_X W` with projections `p : V ⟶ U`, `h : V ⟶ W`. The
Künneth maps (`AlgebraicGeometry.Etale.kunnethMap`) of `(X, Y)` at `Rj_* F` and of `(U, Y)` at
`F` are compatible with the exchange map `β : Lq^* Rj_* F ⟶ Rh_* Lp^* F`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) and the composition isomorphism
`Ra_{X*} Rj_* ≅ Ra_{U*}` (blueprint `lem-kun-bc-kunneth-compat`).

As a consequence, for `S = Spec k` with `k` separably closed and `Λ` a finite ring whose exponent
is invertible in `k`, `RΓ(W, β)` is an isomorphism: this is the projective case of the proof of
blueprint `lem-kun-0f1h`.

## Main statements

- `AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap` (`lem-kun-bc-kunneth-compat`).
- `AlgebraicGeometry.Etale.isIso_rightDerivedGlobalSections_map_derivedBaseChangeMap_of_isProper`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  [HasSmallSiteSheafify A]

variable {S X Y U W V : Scheme.{u}}

/-- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`, written with the derived
tensor product `AlgebraicGeometry.Etale.derivedTensor`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_comp_derivedTensor {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g₁₂).app K).app M ≫
        ((-⊗ᴸ-(T)[A]).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K)).app _ ≫
        ((-⊗ᴸ-(T)[A]).obj _).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app M) =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (((-⊗ᴸ-(R)[A]).obj K).obj M) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ := by
  have := leftDerivedUpperStarTensorComparison_comp A g₁ g₂ g₁₂ hg K M
  rw [MonoidalCategory.tensorHom_def] at this
  exact this

/-- The transpose of the Künneth map `κ_{E,K}` along `Lc^* ⊣ Rc_*`, written with the tensor
comparison of `Lc^*`: it is
`Lc^*(Rf_* E ⊗ᴸ Rg_* K) ⟶ Lc^* Rf_* E ⊗ᴸ Lc^* Rg_* K ⟶ Lp^* E ⊗ᴸ Lq^* K`, the second map being
`Lc^* Rf_* E ≅ Lp^* Lf^* Rf_* E ⟶ Lp^* E` tensored with `Lc^* Rg_* K ≅ Lq^* Lg^* Rg_* K ⟶ Lq^* K`. -/
@[reassoc]
lemma map_kunnethMap_comp_counit (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((c)^*[A]).map (kunnethMap A p q f g c hp hq E K) ≫
        (derivedUpperStarLowerStarAdjunction A c).counit.app _ =
      ((leftDerivedUpperStarTensorComparison A c).app _).app _ ≫
        ((-⊗ᴸ-(W)[A]).map ((leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
          L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E))).app _ ≫
        ((-⊗ᴸ-(W)[A]).obj _).map ((leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K)) := by
  refine ((derivedUpperStarLowerStarAdjunction A c).homEquiv_counit (g := kunnethMap A p q f g c hp hq E K)).symm.trans ?_
  rw [kunnethMap, Equiv.symm_apply_apply,
    ← leftDerivedUpperStarTensorComparison_comp_derivedTensor_assoc A p f c hp.symm]
  congr 1
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map, Category.assoc,
    comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id_app,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  done

/-- Blueprint `lem-kun-bc-kunneth-compat`: compatibility of the Künneth maps with the exchange
map of the square

```
  V --h--> W --r--> Y
  |        |        |
  p        q        a_Y
  v        v        v
  U --j--> X --a_X-> S
```

For `F ∈ D(U_ét)` and `K ∈ D(Y_ét)`, the Künneth map of `(U, Y)` at `(F, K)`, precomposed with
the composition isomorphism `Ra_{X*} Rj_* F ≅ Ra_{U*} F`, is the Künneth map of `(X, Y)` at
`(Rj_* F, K)` followed by `Rc_*` of the exchange map `β : Lq^* Rj_* F ⟶ Rh_* Lp^* F` tensored with
`Lr^* K`, the projection map of `h`, the composition isomorphism `Rc_* Rh_* ≅ Rc'_*` and
`Lh^* Lr^* K ≅ Lr'^* K`. -/
lemma kunnethMap_derivedBaseChangeMap (aX : X ⟶ S) (aY : Y ⟶ S) (aU : U ⟶ S)
    (q : W ⟶ X) (r : W ⟶ Y) (c : W ⟶ S) (hq : q ≫ aX = c) (hr : r ≫ aY = c)
    (j : U ⟶ X) (hj : j ≫ aX = aU) (p : V ⟶ U) (h : V ⟶ W) (sq : CommSq p h j q)
    (r' : V ⟶ Y) (hr' : h ≫ r = r') (c' : V ⟶ S) (hc' : h ≫ c = c')
    (hp : p ≫ aU = c') (hr'c : r' ≫ aY = c')
    (F : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(S)[A]).map ((rightDerivedLowerStarCompIsoOfComp A j aX aU hj).hom.app F)).app
        (R((aY)_*[A]).obj K) ≫ kunnethMap A p r' aU aY c' hp hr'c F K =
      kunnethMap A q r aX aY c hq hr (R((j)_*[A]).obj F) K ≫
        R((c)_*[A]).map
          (((-⊗ᴸ-(W)[A]).map ((derivedBaseChangeMap A sq).app F)).app (L((r)^*[A]).obj K) ≫
            ((rightDerivedLowerStarProjectionMap A h).app _).app _) ≫
        (rightDerivedLowerStarCompIsoOfComp A h c c' hc').hom.app _ ≫
        R((c')_*[A]).map (((-⊗ᴸ-(V)[A]).obj _).map
          ((leftDerivedUpperStarComp A h r r' hr'.symm).inv.app K)) := by
  sorry

end General

section Point

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- The projective case of the proof of blueprint `lem-kun-0f1h`.

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`,
`j : U ⟶ X` an open immersion of `k`-schemes of finite type, `Y` a `k`-scheme of finite type
(e.g. projective), `W = X ×_k Y` with projections `q`, `r`, and `V = U ×_X W` with projections
`p : V ⟶ U`, `h : V ⟶ W`. For every `E ∈ D(U_ét, Λ)` the exchange map
`β : Lq^* Rj_* E ⟶ Rh_* Lp^* E` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`) induces an
isomorphism `RΓ(W, Lq^* Rj_* E) ≅ RΓ(W, Rh_* Lp^* E)`.

Following the blueprint, both sides are computed by the Künneth formula
(`AlgebraicGeometry.Etale.isIso_kunnethMap_of_isSepClosed`) with the unit `Λ_Y` on `Y`, and the
two Künneth maps are related by `AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap`
(`lem-kun-bc-kunneth-compat`). -/
theorem isIso_rightDerivedGlobalSections_map_derivedBaseChangeMap_of_isProper
    {X Y U W V : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (q : W ⟶ X) (r : W ⟶ Y) (sqW : IsPullback q r aX aY)
    (j : U ⟶ X) [IsOpenImmersion j] (p : V ⟶ U) (h : V ⟶ W) (sq : IsPullback p h j q)
    (E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app E)) := by
  sorry

end Point

end Etale

end AlgebraicGeometry
