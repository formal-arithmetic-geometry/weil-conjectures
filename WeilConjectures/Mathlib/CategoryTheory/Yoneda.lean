/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Uniqueness of representing objects, and the Yoneda embedding of a fully faithful functor

Mathlib's `CategoryTheory.Functor.RepresentableBy.uniqueUpToIso` constructs an isomorphism between
two representing objects of the same functor. Here we record that it is the *unique* isomorphism
compatible with the two representations.

## Main statements

- `CategoryTheory.Functor.RepresentableBy.existsUnique_iso`: two representing objects of a functor
  are isomorphic through a unique isomorphism compatible with the representations (blueprints
  `lem-sc-jacobian-unique`, `lem-pc-representable-unique`).
- `CategoryTheory.bijective_yoneda_app_id`: the Yoneda bijection `τ ↦ τ_X(𝟙 X)` and its
  naturality (blueprint `lem-pc-yoneda`).
- `CategoryTheory.Functor.isRepresentable_iff_exists_nonempty_iso`: a presheaf is representable
  iff it is isomorphic to a functor of points (blueprint `def-pc-representable-functor`).
- `CategoryTheory.Functor.FullyFaithful.opCompYonedaObjIso`: for a fully faithful `F`,
  `Hom(F -, F A) ≅ Hom(-, A)`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {Y Y' : C}


end CategoryTheory.Functor.RepresentableBy

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]


end CategoryTheory

namespace CategoryTheory.Functor


end CategoryTheory.Functor

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D] {F : C ⥤ D}

/-- For a fully faithful functor `F`, the functor `T ↦ Hom(F T, F A)` is `T ↦ Hom(T, A)`. This is
the same-universe variant of `CategoryTheory.Functor.FullyFaithful.homNatIso`, which is stated
with `uliftYoneda`. -/
noncomputable def opCompYonedaObjIso (hF : F.FullyFaithful) (A : C) :
    F.op ⋙ yoneda.obj (F.obj A) ≅ yoneda.obj A :=
  NatIso.ofComponents (fun _ ↦ hF.homEquiv.symm.toIso)
    (fun g ↦ by ext x; exact hF.map_injective (by simp))

end CategoryTheory.Functor.FullyFaithful
