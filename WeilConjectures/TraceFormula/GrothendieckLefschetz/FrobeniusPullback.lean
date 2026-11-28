/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.FrobeniusCorrespondenceOperator
public import WeilConjectures.TraceFormula.CompactPullback

/-!
# Pullbacks on compactly supported cohomology along proper morphisms over the base

Let `Λ` be a finite coefficient ring and `s` a scheme. For a proper morphism `u : X ⟶ Y` and
morphisms `a' : Y ⟶ s`, `a : X ⟶ s` with `u ≫ a' = a`, the *pullback along `u`*
```
u^♯ : Ra'_! ⟶ Ra'_! Ru_* Lu^* ≅ Ra'_! Ru_! Lu^* ≅ R(u ≫ a')_! Lu^* = Ra_! Lu^*
```
is built from the unit of `Lu^* ⊣ Ru_*`, the identification `Ru_! ≅ Ru_*` and the composition
isomorphism of the lower shriek (`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`). For
`X = Y` and `a = a'` it is the pullback `AlgebraicGeometry.Etale.lowerShriekPullback` defining the
operators of Frobenius correspondences. The pullbacks are transitive
(`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp_comp_app`).

For an endomorphism `u` of `X` over an automorphism `w` of the base (`u ≫ a = a ≫ w`), `u` is a
morphism over `s` from `a ≫ w` to `a`, and the derived global sections of `R(a ≫ w)_!` and of
`Ra_!` are identified by the composition isomorphism and the Leray isomorphism of the proper
`w` (`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsCompIso`). Two instances of this
construction are compared with other descriptions:

* for an automorphism `g` of `X` over an automorphism `h` of `s` (a cartesian square), the
  pullback along `g` is the compact-support base change
  `AlgebraicGeometry.Etale.compactPullback`
  (`AlgebraicGeometry.Etale.compactPullback_app_eq_map_lowerShriekPullbackOfComp`);
* the pullback along the absolute Frobenius `F_X` of a scheme of characteristic `p`, followed by
  the trivialization `L(F_X)^* ≅ 𝟭`, is the identity
  (`AlgebraicGeometry.Etale.map_lowerShriekPullbackOfComp_comp_iterateFrobenius`).

## Main definitions

- `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`: the pullback `u^♯ : Ra'_! ⟶ Lu^* ⋙ Ra_!`.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsCompIso`: the identification
  `RΓ(s, R(a ≫ w)_! -) ≅ RΓ(s, Ra_! -)` for a proper `w : s ⟶ s`.

## Main results

- `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp_comp_app`: transitivity of the pullbacks.
- `AlgebraicGeometry.Etale.compactPullback_app_eq_map_lowerShriekPullbackOfComp`: the pullback
  along an automorphism over an automorphism of the base is the compact-support base change.
- `AlgebraicGeometry.Etale.map_lowerShriekPullbackOfComp_comp_iterateFrobenius`: the absolute
  Frobenius acts trivially on compactly supported cohomology.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {s : Scheme.{u}}

section Pullback

variable {X Y : Scheme.{u}} {a : X ⟶ s} {a' : Y ⟶ s} [QuasiCompact a] [HasCompactification a]
  [QuasiCompact a'] [HasCompactification a']

/-- The *pullback on compactly supported cohomology* `u^♯ : Ra'_! ⟶ Lu^* ⋙ Ra_!` along a proper
morphism `u : X ⟶ Y` with `u ≫ a' = a`: the composite
```
Ra'_! K ⟶ Ra'_! Ru_* Lu^* K ≅ Ra'_! Ru_! Lu^* K ≅ R(u ≫ a')_! Lu^* K = Ra_! Lu^* K
```
of the unit of `Lu^* ⊣ Ru_*`, the identification `Ru_! ≅ Ru_*` and the composition isomorphism
of the lower shriek. -/
noncomputable def lowerShriekPullbackOfComp (u : X ⟶ Y) [IsProper u] (h : u ≫ a' = a) :
    R(a')_![ModuleCat.{u + 1} Λ] ⟶
      L((u)^*[ModuleCat.{u + 1} Λ]) ⋙ R(a)_![ModuleCat.{u + 1} Λ] :=
  have : HasCompactification (u ≫ a') := by rw [h]; infer_instance
  have : QuasiCompact (u ≫ a') := by rw [h]; infer_instance
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u).inv _ ≫
        (rightDerivedLowerShriekCompIso Λ u a').inv ≫ (rightDerivedLowerShriekCongrIso Λ h).hom)

/-- For an endomorphism over `s`, the pullback `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`
is `AlgebraicGeometry.Etale.lowerShriekPullback`. -/
lemma lowerShriekPullbackOfComp_eq_lowerShriekPullback (u : X ⟶ X) [IsProper u] (h : u ≫ a = a) :
    lowerShriekPullbackOfComp Λ u h = lowerShriekPullback Λ u h :=
  rfl

/-- **Transitivity of the pullbacks**: for proper `u₁ : X ⟶ Y`, `u₂ : Y ⟶ Z` over `s`, the pullback
along `u₁₂ = u₁ ≫ u₂` is the pullback along `u₂` followed by the pullback along `u₁` and the
composition isomorphism `Lu₂^* ⋙ Lu₁^* ≅ Lu₁₂^*`. -/
theorem lowerShriekPullbackOfComp_comp_app {Z : Scheme.{u}} {a'' : Z ⟶ s} [QuasiCompact a'']
    [HasCompactification a''] (u₁ : X ⟶ Y) (u₂ : Y ⟶ Z) (u₁₂ : X ⟶ Z) [IsProper u₁]
    [IsProper u₂] [IsProper u₁₂] (hu : u₁₂ = u₁ ≫ u₂) (h₁ : u₁ ≫ a' = a) (h₂ : u₂ ≫ a'' = a')
    (h₁₂ : u₁₂ ≫ a'' = a)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (lowerShriekPullbackOfComp Λ u₁₂ h₁₂).app K =
      (lowerShriekPullbackOfComp Λ u₂ h₂).app K ≫
        (lowerShriekPullbackOfComp Λ u₁ h₁).app (L((u₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map
            ((leftDerivedUpperStarComp _ u₁ u₂ u₁₂ hu).inv.app K) := by
  sorry

end Pullback

section Base

variable {X : Scheme.{u}} (a : X ⟶ s) [QuasiCompact a] [HasCompactification a]

/-- For a proper `w : s ⟶ s`, the identification `RΓ(s, R(a ≫ w)_! -) ≅ RΓ(s, Ra_! -)` given by
the composition isomorphism `R(a ≫ w)_! ≅ Ra_! ⋙ Rw_!` and the isomorphism
`RΓ(s, Rw_! -) ≅ RΓ(s, -)` of the proper `w`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsIsoOfIsProper`). -/
noncomputable def compactlySupportedGlobalSectionsCompIso (w : s ⟶ s) [IsProper w]
    [HasCompactification (a ≫ w)] [QuasiCompact (a ≫ w)] :
    compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) (a ≫ w) ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekCompIso Λ a w) _ ≪≫
    Functor.isoWhiskerLeft R(a)_![ModuleCat.{u + 1} Λ]
      (compactlySupportedGlobalSectionsIsoOfIsProper (ModuleCat.{u + 1} Λ) w)

/-- **The pullback along an automorphism over an automorphism of the base is the compact-support
base change**: for a cartesian square `g ≫ a = a ≫ h` of automorphisms `g` of `X` and `h` of
`s`, the pullback along `g`, a morphism over `s` from `a ≫ h` to `a`, followed by the
identification `RΓ(s, R(a ≫ h)_! -) ≅ RΓ(s, Ra_! -)`, is the compact-support base change
`AlgebraicGeometry.Etale.compactPullback`. -/
theorem compactPullback_app_eq_map_lowerShriekPullbackOfComp {g : X ⟶ X} {h : s ⟶ s} [IsIso g]
    [IsIso h] (sq : IsPullback g a a h) [HasCompactification (a ≫ h)] [QuasiCompact (a ≫ h)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactPullback Λ sq).app K =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          ((lowerShriekPullbackOfComp Λ g sq.w).app K) ≫
        (compactlySupportedGlobalSectionsCompIso Λ a h).hom.app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  sorry

/-- **The absolute Frobenius acts trivially on compactly supported cohomology**: let `X` and `s`
be schemes of characteristic `p` with absolute `p ^ n`-power Frobenius `F_X` and `F_s`, and let
`w` be an inverse of `F_s`, so that `F_X` is a morphism over `s` from `a` to `a ≫ w`. The
pullback along `F_X`, preceded by the identification `RΓ(s, Ra_! -) ≅ RΓ(s, R(a ≫ w)_! -)` and
followed by the trivialization `L(F_X)^* ≅ L(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`), is the identity of
`RΓ(s, Ra_! M)`. -/
theorem map_lowerShriekPullbackOfComp_comp_iterateFrobenius {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hs : (p : Γ(s, ⊤)) = 0) (n : ℕ) {w : s ⟶ s} [IsProper w]
    [IsProper (X.iterateFrobenius hp hX n)] [HasCompactification (a ≫ w)]
    [QuasiCompact (a ≫ w)] (hw : s.iterateFrobenius hp hs n ≫ w = 𝟙 s)
    (hw' : w ≫ s.iterateFrobenius hp hs n = 𝟙 s)
    (h : X.iterateFrobenius hp hX n ≫ a ≫ w = a)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactlySupportedGlobalSectionsCompIso Λ a w).inv.app M ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          ((lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h).app M ≫
            (R(a)_![ModuleCat.{u + 1} Λ]).map
              ((leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
                leftDerivedUpperStarId _ X).hom.app M)) = 𝟙 _ := by
  sorry

/-- **The operator of a Frobenius correspondence is the global operator**: let `Φ = F_X ≫ g` be
the composite of the absolute Frobenius `F_X` of `X` and an automorphism `g` of `X` over an
automorphism `σ` of `s` inverse to the absolute Frobenius `F_s` (a cartesian square), so that `Φ`
is an endomorphism over `s`. For `v : Lg^* K ⟶ K` and the identification
`κ : LΦ^* ≅ Lg^* ⋙ LF_X^* ≅ Lg^*` given by the trivialization of `L(F_X)^*`, the operator
`T(v ∘ κ) = RΓ_c(X, v ∘ κ) ∘ Φ^♯` is the global operator `RΓ_c(X, v) ∘ g_c^*`. -/
theorem correspondenceOperator_comp_eq_globalOperator {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hs : (p : Γ(s, ⊤)) = 0) (n : ℕ) {Φ g : X ⟶ X} {σ : s ⟶ s}
    [IsProper Φ] [IsProper (X.iterateFrobenius hp hX n)] [IsIso g] [IsIso σ]
    [HasCompactification (a ≫ σ)] [QuasiCompact (a ≫ σ)] (sq : IsPullback g a a σ)
    (hΦ : Φ ≫ a = a) (hFg : Φ = X.iterateFrobenius hp hX n ≫ g)
    (hσ : s.iterateFrobenius hp hs n ≫ σ = 𝟙 s) (hσ' : σ ≫ s.iterateFrobenius hp hs n = 𝟙 s)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : L((g)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    correspondenceOperator Λ Φ hΦ ((leftDerivedUpperStarComp _ _ _ _ hFg).hom.app K ≫
        (leftDerivedUpperStarIterateFrobeniusIso _ hp hX n ≪≫ leftDerivedUpperStarId _ X).hom.app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) ≫ v) =
      globalOperator Λ sq v := by
  have h₁ : X.iterateFrobenius hp hX n ≫ a ≫ σ = a := by
    rw [← Category.assoc, ← comp_iterateFrobenius hp a hs hX, Category.assoc, hσ,
      Category.comp_id]
  have hF := map_lowerShriekPullbackOfComp_comp_iterateFrobenius Λ a hp hX hs n hσ hσ' h₁
    (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hF' := (Iso.inv_comp_eq ((compactlySupportedGlobalSectionsCompIso Λ a σ).app
      (L((g)^*[ModuleCat.{u + 1} Λ]).obj K))).1 hF
  rw [Category.comp_id, Functor.map_comp] at hF'
  rw [correspondenceOperator, globalOperator, ← lowerShriekPullbackOfComp_eq_lowerShriekPullback,
    lowerShriekPullbackOfComp_comp_app Λ _ _ _ hFg h₁ sq.w,
    compactPullback_app_eq_map_lowerShriekPullbackOfComp Λ a sq K]
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]
  rw [reassoc_of% hF']
  rfl

end Base

end AlgebraicGeometry.Etale
