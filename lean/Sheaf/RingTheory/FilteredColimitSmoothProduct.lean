/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import Sheaf.RingTheory.SmoothOverProductRing

/-!
# Filtered colimits of smooth algebras and products

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07F3 (lemma-product)
(blueprint: lem-weil-pbc-popescu-product).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

/-- The product of two filtered colimits of smooth algebras is such a colimit over the
product base ring.

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07F3 (lemma-product).
(blueprint: lem-weil-pbc-popescu-product).

Proof:
1. By def-weil-pbc-filtered-colimit-smooth-algebras, choose small filtered diagrams
   `A : I ⥤ CommAlgCat R₁` and `B : J ⥤ CommAlgCat R₂`, with smooth terms and colimit
   cocones `ιᵢ : Aᵢ → Λ₁` and `κⱼ : Bⱼ → Λ₂` (def-weil-pbc-category-colimit).
   The category `I × J` is nonempty. Common upper objects and equalizers of parallel
   arrows are obtained componentwise, so it is small and filtered.
2. Define `D(i,j) = Aᵢ × Bⱼ` over `R₁ × R₂`, with transition maps the products of the
   component transition maps. Identities and composition hold componentwise. Each term
   is smooth by lem-weil-pbc-smooth-over-product-ring and def-weil-pbc-smooth-ring-map.
3. The maps `θ(i,j) = ιᵢ × κⱼ` are algebra maps to `Λ₁ × Λ₂` for the product structure
   map. Componentwise cocone compatibility makes them a cocone on `D`, in the sense of
   def-weil-pbc-category-colimit.
4. To verify the colimit property, take any cocone `μ(i,j) : D(i,j) → M`. The images
   `e₁,e₂` of `(1,0),(0,1)` in `M` satisfy `e₁ + e₂ = 1`, `e₁ * e₂ = 0` and `eₖ² = eₖ`.
   Thus `Mₖ = eₖM` is a ring with unit `eₖ`, over the corresponding base ring. The maps
   `x ↦ μ(i,j)(x,0)` and `y ↦ μ(i,j)(0,y)` land in `M₁` and `M₂`. The first is independent
   of `j`, since any two objects of `J` map to a common object; the second is independent
   of `i` for the same reason. Their transition compatibility gives cocones on `A` and
   `B`. The original colimit properties give unique algebra maps `uₖ : Λₖ → Mₖ`.
   Define `u(λ₁,λ₂) = u₁(λ₁) + u₂(λ₂)`. Orthogonality gives multiplicativity and
   `e₁ + e₂ = 1` gives preservation of the unit; the structure maps give base compatibility.
   This map factors every `μ(i,j)`. Any other factorization restricts on `(λ₁,0)` and
   `(0,λ₂)` to the same `u₁` and `u₂`, by their uniqueness, and therefore equals `u`.
   This verifies the universal property in def-weil-pbc-category-colimit.
5. The small filtered product diagram has smooth terms and the required colimit cocone,
   so def-weil-pbc-filtered-colimit-smooth-algebras gives the conclusion.

Algebras and index categories live in universe `max u v`, as in the Popescu siblings
(lem-weil-pbc-colimit-standard-smooth-algebras, lem-weil-pbc-popescu-lift-once). -/
theorem ind_smooth_prod
    (R₁ R₂ : Type u) (Λ₁ Λ₂ : Type (max u v))
    [CommRing R₁] [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂]
    [Algebra R₁ Λ₁] [Algebra R₂ Λ₂]
    (h₁ : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R₁ ↦ Algebra.Smooth R₁ B) (CommAlgCat.of R₁ Λ₁))
    (h₂ : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R₂ ↦ Algebra.Smooth R₂ B) (CommAlgCat.of R₂ Λ₂)) :
    letI : Algebra (R₁ × R₂) (Λ₁ × Λ₂) :=
      RingHom.toAlgebra (RingHom.prodMap (algebraMap R₁ Λ₁) (algebraMap R₂ Λ₂))
    ObjectProperty.ind.{max u v} (fun B : CommAlgCat.{max u v} (R₁ × R₂) ↦
      Algebra.Smooth (R₁ × R₂) B) (CommAlgCat.of (R₁ × R₂) (Λ₁ × Λ₂)) := by
  sorry

end Algebra
