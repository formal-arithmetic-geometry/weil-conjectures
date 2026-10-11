/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# The Čech complex of a family of morphisms with values in an additive category

Let `C` be a category, `V` an object of `C` such that `Over V` has finite products, and
`U : ι → Over V` a family of objects over `V`. For a presheaf `P` on `C` with values in a
preadditive category `A` with the relevant products, the (ordered) Čech complex `Č(U, P)` has in
degree `k` the product `∏_y P(U (y 0) ×_V ⋯ ×_V U (y k))` over the tuples
`y : Fin (k + 1) → ι`; the differential is the alternating sum of the restrictions along the
projections forgetting one factor.

This is the coefficient-general version of `CategoryTheory.Presheaf.cechComplex`, whose cochains
are elements of abelian groups. The main result is that `Č(U, P)` is exact in positive degrees
when `P` is an injective presheaf, for *every* family `U`: an injective presheaf is a retract of
the presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)`, whose Čech complex is contracted by inserting, in front
of a tuple of morphisms `g : Z ⟶ U (y 0) ×_V ⋯ ×_V U (y k)`, a morphism `Z ⟶ U j` over `V` chosen
depending only on `Z ⟶ V`.

## Main definitions

- `CategoryTheory.Presheaf.prodCechCosimplicialObject`: the Čech cosimplicial object.
- `CategoryTheory.Presheaf.prodCechComplex`: the Čech complex `Č(U, P)`, as a functor of `P`.

## Main statements

- `CategoryTheory.Presheaf.prodCechComplex_exactAt_of_injective`: the Čech complex of an
  injective presheaf is exact in positive degrees.
-/

@[expose] public section

universe v' u' t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] {ι : Type t}
  {A : Type u'} [Category.{v'} A]

section Complex

variable [Preadditive A] [∀ k : ℕ, HasProductsOfShape (Fin (k + 1) → ι) A]

/-- The Čech cosimplicial object of the family `U` with values in a presheaf `P`, as a functor
of `P`. In degree `k` it is `∏_y P(U (y 0) ×_V ⋯ ×_V U (y k))`, and a map `θ` of the simplex
category acts by `(c_y)_y ↦ (P(cechNerveMap U y θ) (c_{y ∘ θ}))_y`. -/
noncomputable def prodCechCosimplicialObject (U : ι → Over V) :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A where
  obj P :=
    { obj k := ∏ᶜ fun y : Fin (k.len + 1) → ι ↦ P.obj (op (cechNerveObj U y).left)
      map {k m} θ := Pi.lift fun y ↦
        Pi.π _ (y ∘ θ.toOrderHom) ≫ P.map (cechNerveMap U y θ.toOrderHom).left.op
      map_id k := sorry
      map_comp θ θ' := sorry }
  map φ :=
    { app k := Limits.Pi.map fun y ↦ φ.app _
      naturality k m θ := sorry }
  map_id P := sorry
  map_comp φ ψ := sorry

/-- The Čech complex `Č(U, P)` of the family `U` with values in a presheaf `P`, as a functor
of `P`: the alternating coface map complex of
`CategoryTheory.Presheaf.prodCechCosimplicialObject`. -/
noncomputable def prodCechComplex (U : ι → Over V) : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  prodCechCosimplicialObject U ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

end Complex

section Injective

variable [Preadditive A] [∀ k : ℕ, HasProductsOfShape (Fin (k + 1) → ι) A]
  [HasProducts.{max w v} A]

/-- **The Čech complex of an injective presheaf is exact in positive degrees**, for every family
`U` of objects over `V`. -/
theorem prodCechComplex_exactAt_of_injective (U : ι → Over V) [HasZeroObject A] [HasBinaryBiproducts A]
    [HasKernels A] [HasCokernels A] (P : Cᵒᵖ ⥤ A) [Injective P] (q : ℕ) :
    ((prodCechComplex U).obj P).ExactAt (q + 1) :=
  sorry

end Injective

end CategoryTheory.Presheaf
