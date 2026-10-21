module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Braiding equivariance of the unit-tensor composite

Source: main-20261015 blueprint, sec-proetale-coefficients,
`sk-def-sfb-finite-pushforward-pullback/lem-sfb-finite-upper-star-braided.proof.md`,
first paragraph (blueprint: lem-sfb-unit-tensor-braiding).

## Main statements

* `Functor.LaxBraided.tensorHom_μ_braiding`: the lax tensor map after two arbitrary arrows
  commutes with the braidings.
* `Adjunction.unit_tensor_μ_braiding`: the specialization to the adjunction units.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MonoidalCategory

/-- The tensor of two arrows followed by a lax braided tensor map intertwines braidings.

Source: main-20261015 blueprint, `lem-sfb-finite-upper-star-braided.proof.md`, first
paragraph (blueprint: lem-sfb-unit-tensor-braiding).

Proof: precompose `Functor.LaxBraided.braided` at `P,Q` with `u ⊗ₘ v` and reassociate.
Apply `BraidedCategory.braiding_naturality` (lem-sfb-braiding-naturality) to `u,v` to
replace their tensor followed by the braiding on `R.obj P,R.obj Q` with the braiding
on `X,Y` followed by `v ⊗ₘ u`. Substitute and reassociate. These are steps 1--3 of
lem-sfb-unit-tensor-braiding. The composites called `a,b` in the node are written out.
-/
theorem Functor.LaxBraided.tensorHom_μ_braiding
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
    (R : D ⥤ C) [R.LaxBraided] {X Y : C} {P Q : D}
    (u : X ⟶ R.obj P) (v : Y ⟶ R.obj Q) :
    ((u ⊗ₘ v) ≫ Functor.LaxMonoidal.μ R P Q) ≫ R.map (β_ P Q).hom =
      (β_ X Y).hom ≫ ((v ⊗ₘ u) ≫ Functor.LaxMonoidal.μ R Q P) := by
  rw [Category.assoc, Functor.LaxBraided.braided,
    ← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]

/-- The tensor of adjunction units followed by the right adjoint's lax tensor map
intertwines braidings.

Source: main-20261015 blueprint, `lem-sfb-finite-upper-star-braided.proof.md`, first
paragraph (blueprint: lem-sfb-unit-tensor-braiding).

Proof: steps 1--3 are the calculation in
`Functor.LaxBraided.tensorHom_μ_braiding`: precompose the braided identity, apply
lem-sfb-braiding-naturality, and reassociate. For step 4 substitute `P = L.obj X`,
`Q = L.obj Y`, `u = adj.unit.app X`, `v = adj.unit.app Y` in that formula.
The unit is the image of the identity under the adjunction's natural Hom equivalence.
No monoidal structure on `L` or monoidal compatibility of the adjunction is needed.
-/
theorem Adjunction.unit_tensor_μ_braiding
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxBraided] (adj : L ⊣ R) (X Y : C) :
    ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫
        Functor.LaxMonoidal.μ R (L.obj X) (L.obj Y)) ≫
        R.map (β_ (L.obj X) (L.obj Y)).hom =
      (β_ X Y).hom ≫ ((adj.unit.app Y ⊗ₘ adj.unit.app X) ≫
        Functor.LaxMonoidal.μ R (L.obj Y) (L.obj X)) := by
  exact Functor.LaxBraided.tensorHom_μ_braiding R (adj.unit.app X) (adj.unit.app Y)

end CategoryTheory
