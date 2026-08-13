/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Naturality of `Proj.toSpecZero` with respect to `Proj.map`

We record that `Proj.map` only depends on the underlying graded ring homomorphism, and the
naturality of `Proj.toSpecZero` with respect to `Proj.map`.
-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `Proj.map` only depends on the underlying graded ring homomorphism. -/
lemma Proj.map_congr {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst e; rfl

/-- Naturality of `Proj.toSpecZero` with respect to `Proj.map`: the square

```
Proj ℬ  ⟶  Proj 𝒜
  |            |
  v            v
Spec (ℬ 0) ⟶ Spec (𝒜 0)
```

commutes. -/
lemma Proj.map_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradeZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2, Proj.awayι_toSpecZero,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    HomogeneousLocalization.Away.map_comp_fromZeroRingHom]

end AlgebraicGeometry
