/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!
# The composition law of the compactly supported direct image

For torsion coefficients `Λ` and morphisms `f : X ⟶ Y`, `g : Y ⟶ T` admitting
compactifications, the compactly supported direct images satisfy
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on the unbounded derived categories of étale sheaves.

Comparing compactifications usually goes through the closure of `X` in a product of two of
them, which needs `f` to be quasi-compact. Here no closure is taken. Instead `Rf_!` is computed
through any proper `π : P ⟶ Y` and any factorisation of `f` as a proper `h : X ⟶ U` followed
by an open immersion `e : U ⟶ P` and `π`: `Rf_! ≅ Rh_* ⋙ De_! ⋙ Rπ_*`. This uses only the
exchange isomorphism `Rg'_* ⋙ Dj_! ≅ Dj'_! ⋙ Rg''_*` for a cartesian square with `j`
open and `g''` proper
(`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`),
applied to the graphs of `X` in fibre products. In particular, a proper `h` factoring through
an open immersion `u` as `h' ≫ u` satisfies `Rh'_* ⋙ Du_! ≅ Rh_*`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriekOfCompactification`:
  `Rf_!(c) ≅ Rh_* ⋙ De_! ⋙ Rπ_*` for every compactification `c` of `f`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`: the
  composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The extension by zero along the identity is the identity: both are left adjoint to
`(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def openImmersionLowerShriekId (X : Scheme.{u}) : (𝟙 X)_!open[A] ≅ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction A (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (upperStarId A X).symm)

/-- The derived extension by zero along the identity is the identity. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekId (X : Scheme.{u}) :
    D((𝟙 X)_!open[A]) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekId A X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The composition isomorphism `D(k_!) ≅ D(j'_!) ⋙ D(j_!)` of derived extensions by zero, for
open immersions with `j' ≫ j = k`. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekComp {V U X : Scheme.{u}}
    (j' : V ⟶ U) (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsOpenImmersion k] (w : j' ≫ j = k) :
    D((k)_!open[A]) ≅ D((j')_!open[A]) ⋙ D((j)_!open[A]) := by
  subst w
  exact Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComp A j' j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ Rg_*` for `g₁ ≫ g₂ = g`. -/
noncomputable def rightDerivedLowerStarCompOfEq {T S U : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ U)
    (g : T ⟶ U) (w : g₁ ≫ g₂ = g) : R((g₁)_*[A]) ⋙ R((g₂)_*[A]) ≅ R((g)_*[A]) := by
  subst w
  exact rightDerivedLowerStarComp A g₁ g₂

end General

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The derived direct image along the identity is the identity. -/
noncomputable def rightDerivedLowerStarIdIsoOfFinite (Y : Scheme.{u}) :
    R((𝟙 Y)_*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  (Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- **Exchange of an extension by zero with a proper direct image**, for torsion coefficients:
for a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions and `g''` proper,
`Rg'_* ⋙ Dj_! ≅ Dj'_! ⋙ Rg''_*`. -/
noncomputable def openImmersionLowerShriekLowerStarExchangeIso {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] [IsProper g''] (hsq : IsPullback g' j' j g'') :
    R((g')_*[ModuleCat.{u + 1} Λ]) ⋙ D((j)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((j')_!open[ModuleCat.{u + 1} Λ]) ⋙ R((g'')_*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite hsq
  asIso (openImmersionLowerShriekLowerStarExchange _ hsq)

/-- **Extension by zero of a proper direct image.** If a proper morphism `h : X ⟶ U` factors
as `h' ≫ u` through an open immersion `u : U' ⟶ U`, then `Rh'_* ⋙ Du_! ≅ Rh_*`, for torsion
coefficients. This is the exchange isomorphism for the cartesian square
`h' ≫ u = 𝟙 X ≫ h`. -/
noncomputable def rightDerivedLowerStarCompOpenImmersionLowerShriekIso {X U' U : Scheme.{u}}
    (h' : X ⟶ U') (u : U' ⟶ U) [IsOpenImmersion u] (h : X ⟶ U) [IsProper h]
    (w : h' ≫ u = h) :
    R((h')_*[ModuleCat.{u + 1} Λ]) ⋙ D((u)_!open[ModuleCat.{u + 1} Λ]) ≅
      R((h)_*[ModuleCat.{u + 1} Λ]) :=
  openImmersionLowerShriekLowerStarExchangeIso Λ
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 X) ⟨by simp [w]⟩) ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryOpenImmersionLowerShriekId _ X) _ ≪≫
    Functor.leftUnitor _

/-- **`Rf_!` through a proper map with a locally closed factorisation.** Let `c` be a
compactification of `f : X ⟶ Y`, let `π : P ⟶ Y` be proper and let `f = h ≫ e ≫ π` with
`e : U ⟶ P` an open immersion and `h : X ⟶ U` proper. Then `Rf_!(c) ≅ Rh_* ⋙ De_! ⋙ Rπ_*`, for
torsion coefficients.

Both sides are compared with `X` embedded in `P ×_Y Z`, `Z` the compactification of `c`, by
the exchange isomorphism for the open immersions `P ×_Y X ⟶ P ×_Y Z` and
`U ×_Y Z ⟶ P ×_Y Z`, along the proper projections to `Z` and to `P`; on their intersection
the two embeddings of `X` agree. No quasi-compactness of `f` is needed. -/
theorem nonempty_iso_rightDerivedLowerShriekOfCompactification {X Y P U : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (π : P ⟶ Y) [IsProper π] (e : U ⟶ P)
    [IsOpenImmersion e] (h : X ⟶ U) [IsProper h] (fac : h ≫ e ≫ π = f) :
    Nonempty (Rf_!(c)[ModuleCat.{u + 1} Λ] ≅
      R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ D((e)_!open[ModuleCat.{u + 1} Λ]) ⋙
        R((π)_*[ModuleCat.{u + 1} Λ])) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let p₁ := pullback.fst π c.g
  let p₂ := pullback.snd π c.g
  have : IsProper p₁ := MorphismProperty.pullback_fst _ _ c.isProper
  have : IsProper p₂ := MorphismProperty.pullback_snd _ _ ‹IsProper π›
  let ι : X ⟶ pullback π c.g := pullback.lift (h ≫ e) c.i (by
    rw [Category.assoc, fac]; exact c.comm)
  -- the graph of `X` in `P ×_Y X`, open in `P ×_Y Z`
  let a₁ := pullback.fst p₂ c.i
  let s₁ := pullback.snd p₂ c.i
  have : IsSeparated s₁ := MorphismProperty.pullback_snd _ _ inferInstance
  let Γ₁ : X ⟶ pullback p₂ c.i := pullback.lift ι (𝟙 X) (by simp [ι, p₂])
  have : IsProper (Γ₁ ≫ s₁) := by rw [show Γ₁ ≫ s₁ = 𝟙 X from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper Γ₁ := IsProper.of_comp Γ₁ s₁
  -- `X` in `U ×_Y Z`, open in `P ×_Y Z`
  let a₂ := pullback.fst p₁ e
  let s₂ := pullback.snd p₁ e
  have : IsSeparated s₂ := MorphismProperty.pullback_snd _ _ inferInstance
  let h₂ : X ⟶ pullback p₁ e := pullback.lift ι h (by simp [ι, p₁])
  have : IsProper (h₂ ≫ s₂) := by rw [show h₂ ≫ s₂ = h from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper h₂ := IsProper.of_comp h₂ s₂
  -- the intersection of the two opens
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let γ : X ⟶ pullback a₁ a₂ := pullback.lift Γ₁ h₂ (by simp [Γ₁, h₂, a₁, a₂])
  let eΓ : R((γ)_*[𝔸]) ⋙ D((b₁)_!open[𝔸]) ≅ R((Γ₁)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ γ b₁ Γ₁ (pullback.lift_fst _ _ _)
  let eh : R((γ)_*[𝔸]) ⋙ D((b₂)_!open[𝔸]) ≅ R((h₂)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ γ b₂ h₂ (pullback.lift_snd _ _ _)
  -- the two extensions by zero agree
  let eC : R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ≅ R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) :=
    Functor.isoWhiskerRight eΓ.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₁ a₁ (b₁ ≫ a₁) rfl).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₂ a₂ (b₁ ≫ a₁)
            pullback.condition.symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eh _
  -- the side of `c`
  let eA : Rf_!(c)[𝔸] ≅ R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ⋙ R((p₁ ≫ π)_*[𝔸]) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight ((rightDerivedLowerStarIdIsoOfFinite Λ X).symm ≪≫
        (rightDerivedLowerStarCompOfEq 𝔸 Γ₁ s₁ (𝟙 X) (pullback.lift_snd _ _ _)).symm) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso Λ
          (IsPullback.of_hasPullback p₂ c.i).flip) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq 𝔸 p₂ c.g (p₁ ≫ π)
          pullback.condition.symm))
  -- the side of `π`
  let eB : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((π)_*[𝔸]) ≅
      R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) ⋙ R((p₁ ≫ π)_*[𝔸]) :=
    Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq 𝔸 h₂ s₂ h
        (pullback.lift_snd _ _ _)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso Λ
          (IsPullback.of_hasPullback p₁ e).flip) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq 𝔸 p₁ π (p₁ ≫ π) rfl))
  exact ⟨eA ≪≫ (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eC _ ≪≫
    Functor.associator _ _ _ ≪≫ eB.symm⟩

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the compactly supported direct image, for
torsion coefficients, each side computed with the chosen compactifications. No
quasi-compactness is needed.

With `X ⟶[k] V ⟶[r] T` and `Y ⟶[j] W ⟶[q] T` the compactifications of `f ≫ g` and `g`, the
scheme `P = V ×_T W` is proper over `T` and over `W`, and `X` sits in it as a closed subscheme
of the open `P ×_V X`. By `nonempty_iso_rightDerivedLowerShriekOfCompactification`,
`R(f ≫ g)_!` is computed in `P`. Over the open `Y ⊆ W` the same embedding computes `Rf_!` in
`P ×_W Y`, which is proper over `Y`, and the exchange isomorphism for the open immersion
`P ×_W Y ⟶ P` along the proper `P ⟶ W` moves `Dj_!` past the direct image. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ T) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let cfg := HasCompactification.compactification (f ≫ g)
  -- `P = V ×_T W`
  let φ := pullback.fst cfg.g cg.g
  let ψ := pullback.snd cfg.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ cfg.isProper
  -- `X` in the open `P ×_V X` of `P`
  let e := pullback.fst φ cfg.i
  let σ := pullback.snd φ cfg.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w₁ : cfg.i ≫ cfg.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← cfg.comm, Category.assoc, ← cg.comm]
  let h : X ⟶ pullback φ cfg.i :=
    pullback.lift (pullback.lift cfg.i (f ≫ cg.i) w₁) (𝟙 X) (by simp [φ])
  have : IsProper (h ≫ σ) := by rw [show h ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
                                infer_instance
  have : IsProper h := IsProper.of_comp h σ
  have he : h ≫ e = pullback.lift cfg.i (f ≫ cg.i) w₁ := pullback.lift_fst _ _ _
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerShriekOfCompactification Λ cfg (ψ ≫ cg.g) e h
    (by rw [reassoc_of% he, pullback.lift_snd_assoc, Category.assoc, ← cg.comm])
  -- `P ×_W Y`, open in `P` and proper over `Y`
  let eY := pullback.fst ψ cg.i
  let πY := pullback.snd ψ cg.i
  have : IsProper πY := MorphismProperty.pullback_snd _ _ inferInstance
  let uY := pullback.fst e eY
  let e' := pullback.snd e eY
  let ρ : X ⟶ pullback ψ cg.i := pullback.lift (h ≫ e) f (by rw [he]; simp [ψ])
  let h' : X ⟶ pullback e eY := pullback.lift h ρ (by simp [ρ, eY])
  have : IsProper (h' ≫ uY) := by rw [show h' ≫ uY = h from pullback.lift_fst _ _ _]
                                  infer_instance
  have : IsProper h' := IsProper.of_comp h' uY
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerShriekOfCompactification Λ cf πY e' h'
    (by simp [h', e', ρ, πY])
  let eh : R((h')_*[𝔸]) ⋙ D((uY)_!open[𝔸]) ≅ R((h)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ h' uY h (pullback.lift_fst _ _ _)
  let ex : R((πY)_*[𝔸]) ⋙ D((cg.i)_!open[𝔸]) ≅ D((eY)_!open[𝔸]) ⋙ R((ψ)_*[𝔸]) :=
    openImmersionLowerShriekLowerStarExchangeIso Λ (IsPullback.of_hasPullback ψ cg.i).flip
  let e₃ : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸]) ≅
      (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸]) ⋙ R((πY)_*[𝔸])) ⋙ D((cg.i)_!open[𝔸]) ⋙
        R((cg.g)_*[𝔸]) :=
    Functor.isoWhiskerRight eh.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 uY e (uY ≫ e) rfl).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 e' eY (uY ≫ e)
              pullback.condition.symm) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
            (rightDerivedLowerStarCompOfEq 𝔸 ψ cg.g _ rfl).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ex.symm _ ≪≫
          Functor.associator _ _ _)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _
  exact ⟨e₁ ≪≫ e₃ ≪≫ Functor.isoWhiskerRight e₂.symm _⟩

end Torsion

end Etale

end AlgebraicGeometry
