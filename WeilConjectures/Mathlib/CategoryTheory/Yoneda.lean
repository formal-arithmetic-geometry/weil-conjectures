/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Uniqueness of representing objects

Mathlib's `CategoryTheory.Functor.RepresentableBy.uniqueUpToIso` constructs an isomorphism between
two representing objects of the same functor. Here we record that it is the *unique* isomorphism
compatible with the two representations.

## Main statements

- `CategoryTheory.Functor.RepresentableBy.existsUnique_iso`: two representing objects of a functor
  are isomorphic through a unique isomorphism compatible with the representations (blueprint
  `lem-sc-jacobian-unique`).
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {Y Y' : C}

/-- The isomorphism `e.uniqueUpToIso e' : Y ≅ Y'` between two representing objects of `F` is
compatible with the representations: the triangle
```
  (X ⟶ Y) --(· ≫ u.hom)--> (X ⟶ Y')
        \                     /
       e.homEquiv      e'.homEquiv
           \               /
            --->  F(X)  <--
```
commutes, where `u = e.uniqueUpToIso e'`. -/
lemma homEquiv_comp_uniqueUpToIso_hom (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y')
    {X : C} (f : X ⟶ Y) : e'.homEquiv (f ≫ (e.uniqueUpToIso e').hom) = e.homEquiv f := by
  have h : (e.uniqueUpToIso e').hom = e'.homEquiv.symm (e.homEquiv (𝟙 Y)) := by
    simp [uniqueUpToIso, Yoneda.ext]
    rfl
  rw [h, e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.comp_id]

/-- **Uniqueness of the representing object.** If `(Y, e)` and `(Y', e')` both represent `F`, there
is a unique isomorphism `u : Y ≅ Y'` with `e' ∘ h_u = e`, i.e. `e'.homEquiv (f ≫ u.hom) =
e.homEquiv f` for every `f : X ⟶ Y`: `u` is the unique isomorphism making the triangle
```
  (X ⟶ Y) --(· ≫ u.hom)--> (X ⟶ Y')
        \                     /
       e.homEquiv      e'.homEquiv
           \               /
            --->  F(X)  <--
```
commute for every `X`.

For the functor `Pic^0_{C/k}` this is the uniqueness of the Jacobian; that `u` is a homomorphism
of group schemes is not part of the statement, as `Pic^0_{C/k}` is only a functor to types here.

(blueprint: `lem-sc-jacobian-unique`) -/
theorem existsUnique_iso (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') :
    ∃! u : Y ≅ Y', ∀ {X : C} (f : X ⟶ Y), e'.homEquiv (f ≫ u.hom) = e.homEquiv f := by
  refine ⟨e.uniqueUpToIso e', fun f ↦ homEquiv_comp_uniqueUpToIso_hom e e' f, fun u hu ↦ ?_⟩
  ext
  apply e'.homEquiv.injective
  rw [← Category.id_comp u.hom, hu, ← Category.id_comp (e.uniqueUpToIso e').hom,
    homEquiv_comp_uniqueUpToIso_hom]

end CategoryTheory.Functor.RepresentableBy
