/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Evaluation functors for spectral objects

We record the evaluation functors `SpectralObject.hFunctor n D : SpectralObject C ι ⥤ C`
and a criterion for the map `Hⁿ(f) ⟶ Hⁿ(f ≫ g)` to be an isomorphism.

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian.SpectralObject

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

end Abelian.SpectralObject

end CategoryTheory
