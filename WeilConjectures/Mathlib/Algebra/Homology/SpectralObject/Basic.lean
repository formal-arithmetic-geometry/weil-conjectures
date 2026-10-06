/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Images of spectral objects under exact functors

Let `γ : C ⥤ C'` be a functor between abelian categories which preserves homology
(e.g. an exact functor). Given a spectral object `Y : SpectralObject C ι`, we define the
spectral object `Y.mapExactFunctor γ : SpectralObject C' ι` obtained by composing
with `γ`, and the corresponding functor
`γ.mapAbelianSpectralObject ι : SpectralObject C ι ⥤ SpectralObject C' ι`.

We also record the evaluation functors `SpectralObject.hFunctor n D : SpectralObject C ι ⥤ C`
and a criterion for the map `Hⁿ(f) ⟶ Hⁿ(f ≫ g)` to be an isomorphism.

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace ComposableArrows

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']

/-- The image of an exact sequence `mk₂ f g` under a functor which preserves
homology is exact. -/
lemma Exact.map_mk₂ {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (h : (mk₂ f g).Exact)
    (γ : C ⥤ C') [γ.PreservesZeroMorphisms] [γ.PreservesHomology] :
    (mk₂ (γ.map f) (γ.map g)).Exact :=
  ((h.exact 0).map γ).exact_toComposableArrows

end ComposableArrows

namespace Abelian.SpectralObject

section

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]

/-- The functor `Y ↦ Hⁿ(D)` evaluating a spectral object at the degree `n` and the arrow `D`. -/
@[simps]
def hFunctor (n : ℤ) (D : ComposableArrows ι 1) : SpectralObject C ι ⥤ C where
  obj Y := (Y.H n).obj D
  map φ := (φ.hom n).app D

/-- If `hⁿ⁻¹(g)` and `hⁿ(g)` vanish, then the map `hⁿ(f) ⟶ hⁿ(f ≫ g)` is an isomorphism. -/
lemma isIso_H_map_twoδ₂Toδ₁ (X : SpectralObject C ι)
    (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i₀ i₁ i₂ : ι} (f : i₀ ⟶ i₁) (g : i₁ ⟶ i₂) (fg : i₀ ⟶ i₂)
    (hfg : f ≫ g = fg) (h₀ : IsZero ((X.H n₀).obj (mk₁ g)))
    (h₁ : IsZero ((X.H n₁).obj (mk₁ g))) :
    IsIso ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) := by
  have : Mono ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) :=
    (X.exact₁ f g fg hfg n₀ n₁ hn₁).mono_g (h₀.eq_of_src _ _)
  have : Epi ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) :=
    (X.exact₂ f g fg hfg n₁).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end

end Abelian.SpectralObject

namespace Abelian.SpectralObject

variable {C C' ι : Type*} [Category* C] [Category* C'] [Category* ι] [Abelian C] [Abelian C']

/-- The image of a spectral object under a functor which preserves homology
(e.g. an exact functor). -/
def mapExactFunctor (Y : SpectralObject C ι) (γ : C ⥤ C')
    [γ.PreservesZeroMorphisms] [γ.PreservesHomology] : SpectralObject C' ι where
  H n := Y.H n ⋙ γ
  δ' n₀ n₁ h := Functor.whiskerRight (Y.δ' n₀ n₁ h) γ
  exact₁' n₀ n₁ h D := (Y.exact₁' n₀ n₁ h D).map_mk₂ γ
  exact₂' n D := (Y.exact₂' n D).map_mk₂ γ
  exact₃' n₀ n₁ h D := (Y.exact₃' n₀ n₁ h D).map_mk₂ γ

variable (Y : SpectralObject C ι) (γ : C ⥤ C') [γ.PreservesZeroMorphisms] [γ.PreservesHomology]

@[simp]
lemma mapExactFunctor_H (n : ℤ) : (Y.mapExactFunctor γ).H n = Y.H n ⋙ γ := rfl

@[simp]
lemma mapExactFunctor_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    (Y.mapExactFunctor γ).δ f g n₀ n₁ h = γ.map (Y.δ f g n₀ n₁ h) := rfl

end Abelian.SpectralObject

namespace Functor

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']

/-- The functor between categories of spectral objects in abelian categories that is
induced by a functor which preserves homology (e.g. an exact functor). -/
@[simps]
def mapAbelianSpectralObject (γ : C ⥤ C') [γ.PreservesZeroMorphisms]
    [γ.PreservesHomology] (ι : Type*) [Category* ι] :
    Abelian.SpectralObject C ι ⥤ Abelian.SpectralObject C' ι where
  obj Y := Y.mapExactFunctor γ
  map α :=
    { hom n := Functor.whiskerRight (α.hom n) γ
      comm n₀ n₁ h i j k f g := by
        simp only [Abelian.SpectralObject.mapExactFunctor_δ, whiskerRight_app, ← γ.map_comp,
          Abelian.SpectralObject.Hom.comm] }

end Functor

end CategoryTheory
