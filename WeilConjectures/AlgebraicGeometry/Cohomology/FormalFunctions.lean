/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# The theorem on formal functions, in degree zero

Let `f : W ⟶ T` be a proper morphism of schemes, let `F` be a coherent sheaf of `𝒪_W`-modules
and let `t` be a point of `T`. Writing `T_n = Spec (𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` for the `n`-th
infinitesimal neighbourhood of `t` and `F^{(n)}` for the pullback of `F` to `W ×_T T_n`, the
theorem on formal functions compares the `𝔪_t`-adic completion of the stalk `(f_* F)_t` with
the inverse limit of the modules `Γ(W ×_T T_n, F^{(n)})`.

This file sets up the two sides of that comparison: the completed stalk, and the modules of
sections over the infinitesimal base changes.

## Main definitions

- `AlgebraicGeometry.Scheme.infinitesimalBaseChange`: the base change `W ×_T T_n` of a morphism
  `f : W ⟶ T` along the `n`-th infinitesimal neighbourhood of a point `t` of `T`, together with
  its projection to `W`, the transition morphisms `W ×_T T_m ⟶ W ×_T T_n` for `m ≤ n` and the
  fact that every point of `W ×_T T_n` lies over `t`.
- `AlgebraicGeometry.Scheme.Modules.formalSections`: the module `Γ(W ×_T T_n, F^{(n)})` of
  sections of the pullback of `F` to `W ×_T T_n`, as a module over the local ring `𝒪_{T, t}`,
  and `AlgebraicGeometry.Scheme.Modules.formalSectionsFun`, the transition map of the inverse
  system `n ↦ Γ(W ×_T T_n, F^{(n)})`.
- `AlgebraicGeometry.Scheme.Modules.completedStalk`: the `𝔪_t`-adic completion of the stalk of
  a sheaf of `𝒪_T`-modules at `t`, which is the left-hand side of the comparison. By
  `AlgebraicGeometry.Scheme.Modules.finite_stalk` the stalk of a coherent sheaf is a finite
  module over `𝒪_{T, t}`, so over a noetherian scheme the completion is the completion of a
  finite module over a noetherian local ring.

## TODO

State `prop:cube-formal-functions`: for `T` noetherian, `f` proper and `F` coherent, the
canonical map from the completed stalk of `f_* F` to `lim_n Γ(W ×_T T_n, F^{(n)})` is an
isomorphism (the degree-zero case of [Stacks, 02OC], to be stated with a `sorry`, as
`prop:cube-proper-pushforward-coherent` is in
`WeilConjectures.AlgebraicGeometry.Cohomology.Proper`). What is still missing is the
`𝒪_{T, t}`-linearity of `formalSectionsFun`, the resulting inverse system `ℕᵒᵖ ⥤ ModuleCat
𝒪_{T, t}`, and the comparison map out of the completion, which factors the maps
`(f_* F)_t ⟶ Γ(W ×_T T_n, F^{(n)})` through the quotients by `𝔪_t ^ (n + 1)`.

## References

* [Stacks, 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, Theorem 11.1

## Blueprint

This file works towards `prop:cube-formal-functions` of the chapter on the theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme

section BaseChange

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- The base change `W ×_T T_n` of `f : W ⟶ T` along the `n`-th infinitesimal neighbourhood
of `t`. -/
noncomputable abbrev infinitesimalBaseChange (n : ℕ) : Scheme.{u} :=
  Limits.pullback f (T.fromInfinitesimalNeighborhood t n)

/-- The projection `W ×_T T_n ⟶ W`. -/
noncomputable abbrev infinitesimalBaseChangeπ (n : ℕ) : infinitesimalBaseChange f t n ⟶ W :=
  Limits.pullback.fst _ _

/-- For `m ≤ n`, the morphism `W ×_T T_m ⟶ W ×_T T_n` induced by `T_m ⟶ T_n`. -/
noncomputable def infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChange f t m ⟶ infinitesimalBaseChange f t n :=
  Limits.pullback.map _ _ _ _ (𝟙 W) (T.infinitesimalNeighborhoodMap t h) (𝟙 T) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_π {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeπ f t n =
      infinitesimalBaseChangeπ f t m := by
  simp [infinitesimalBaseChangeMap]

/-- Every point of `W ×_T T_n` lies over `t`. -/
lemma f_infinitesimalBaseChangeπ_apply (n : ℕ) (w : infinitesimalBaseChange f t n) :
    f (infinitesimalBaseChangeπ f t n w) = t := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply,
    T.fromInfinitesimalNeighborhood_apply]

/-- `W ×_T T_n` lies over any open neighbourhood of `t`. -/
lemma preimage_infinitesimalBaseChangeπ_eq_top (n : ℕ) {U : T.Opens} (hU : t ∈ U) :
    infinitesimalBaseChangeπ f t n ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  ext w
  simpa [f_infinitesimalBaseChangeπ_apply f t n w] using hU

end BaseChange

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

section PushforwardPullback

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules)

end PushforwardPullback

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

section FormalSections

open Limits

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T) (F : W.Modules)

/-- The structure morphism `W ×_T T_n ⟶ T_n`. -/
noncomputable abbrev infinitesimalBaseChangeρ (n : ℕ) :
    infinitesimalBaseChange f t n ⟶ T.infinitesimalNeighborhood t n :=
  pullback.snd _ _

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_ρ {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeρ f t n =
      infinitesimalBaseChangeρ f t m ≫ T.infinitesimalNeighborhoodMap t h := by
  simp [infinitesimalBaseChangeMap]

/-- The ring homomorphism `𝒪_{T, t} ⟶ Γ(W ×_T T_n, 𝒪)`, through which `𝒪_{T, t}` acts on the
sections of the pullback of `F` to `W ×_T T_n`. -/
noncomputable def toInfinitesimalBaseChangeΓ (n : ℕ) :
    T.presheaf.stalk t ⟶ Γ(infinitesimalBaseChange f t n, ⊤) :=
  T.toInfinitesimalRing t n ≫ (Scheme.ΓSpecIso _).inv ≫ (infinitesimalBaseChangeρ f t n).appTop

@[reassoc (attr := simp)]
lemma toInfinitesimalBaseChangeΓ_comp_appTop {m n : ℕ} (h : m ≤ n) :
    toInfinitesimalBaseChangeΓ f t n ≫ (infinitesimalBaseChangeMap f t h).appTop =
      toInfinitesimalBaseChangeΓ f t m := by
  rw [toInfinitesimalBaseChangeΓ, toInfinitesimalBaseChangeΓ, Category.assoc, Category.assoc,
    ← Scheme.Hom.comp_appTop, infinitesimalBaseChangeMap_ρ, Scheme.Hom.comp_appTop,
    ← Category.assoc ((Scheme.ΓSpecIso _).inv), Scheme.infinitesimalNeighborhoodMap,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc,
    Scheme.toInfinitesimalRing_infinitesimalRingMap, Category.assoc]

/-- The comparison isomorphism `u^* F^{(n)} ≅ F^{(m)}` between the pullback of `F^{(n)}` along
`W ×_T T_m ⟶ W ×_T T_n` and `F^{(m)}`. -/
noncomputable def infinitesimalPullbackCompIso {m n : ℕ} (h : m ≤ n) :
    (pullback (infinitesimalBaseChangeMap f t h)).obj
        ((pullback (infinitesimalBaseChangeπ f t n)).obj F) ≅
      (pullback (infinitesimalBaseChangeπ f t m)).obj F :=
  (pullbackComp _ _).app F ≪≫ (pullbackCongr (infinitesimalBaseChangeMap_π f t h)).app F

/-- `Γ(W ×_T T_n, F^{(n)})`, as a module over the local ring `𝒪_{T, t}`. -/
noncomputable def formalSections (n : ℕ) : ModuleCat (T.presheaf.stalk t) :=
  (ModuleCat.restrictScalars (toInfinitesimalBaseChangeΓ f t n).hom).obj
    ((SheafOfModules.evaluation (infinitesimalBaseChange f t n).ringCatSheaf (op ⊤)).obj
      ((pullback (infinitesimalBaseChangeπ f t n)).obj F))

/-- The transition function of the inverse system: the pullback of sections along
`W ×_T T_m ⟶ W ×_T T_n`, followed by the identification of the pullback of `F^{(n)}` with
`F^{(m)}`. -/
noncomputable def formalSectionsFun {m n : ℕ} (h : m ≤ n)
    (s : Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤)) :
    Γ((pullback (infinitesimalBaseChangeπ f t m)).obj F, ⊤) :=
  (infinitesimalPullbackCompIso f t F h).hom.app ⊤
    (sectionsPullback (infinitesimalBaseChangeMap f t h)
      ((pullback (infinitesimalBaseChangeπ f t n)).obj F) s)


/-- The `𝔪_t`-adic completion of the stalk of a sheaf of `𝒪_T`-modules `G` at `t`. This is the
left-hand side of the theorem on formal functions, for `G = f_* F`. -/
noncomputable abbrev completedStalk (G : T.Modules) : Type u :=
  AdicCompletion (maximalIdeal (T.presheaf.stalk t)) (G.presheaf.stalk t)

/-- The canonical map from the stalk of `G` at `t` to its `𝔪_t`-adic completion. -/
noncomputable abbrev toCompletedStalk (G : T.Modules) :
    G.presheaf.stalk t →ₗ[T.presheaf.stalk t] completedStalk t G :=
  AdicCompletion.of _ _

end FormalSections

end AlgebraicGeometry.Scheme.Modules
