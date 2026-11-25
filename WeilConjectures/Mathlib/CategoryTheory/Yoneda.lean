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
  are isomorphic through a unique isomorphism compatible with the representations.
- `CategoryTheory.bijective_yoneda_app_id`: the Yoneda bijection `τ ↦ τ_X(𝟙 X)` and its
  naturality.
- `CategoryTheory.Functor.isRepresentable_iff_exists_nonempty_iso`: a presheaf is representable
  iff it is isomorphic to a functor of points.
- `CategoryTheory.Functor.FullyFaithful.opCompYonedaObjIso`: for a fully faithful `F`,
  `Hom(F -, F A) ≅ Hom(-, A)`.

## Implementation details

`CategoryTheory.bijective_yoneda_app_id` packages Mathlib's `CategoryTheory.yonedaEquiv` with
`CategoryTheory.yonedaEquiv_naturality` and `CategoryTheory.yonedaEquiv_comp`.
`CategoryTheory.Functor.FullyFaithful.opCompYonedaObjIso` is the same-universe variant of
`CategoryTheory.Functor.FullyFaithful.homNatIso`, which is stated with `uliftYoneda`.
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
commute for every `X`. -/
theorem existsUnique_iso (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') :
    ∃! u : Y ≅ Y', ∀ {X : C} (f : X ⟶ Y), e'.homEquiv (f ≫ u.hom) = e.homEquiv f := by
  refine ⟨e.uniqueUpToIso e', fun f ↦ homEquiv_comp_uniqueUpToIso_hom e e' f, fun u hu ↦ ?_⟩
  ext
  apply e'.homEquiv.injective
  rw [← Category.id_comp u.hom, hu, ← Category.id_comp (e.uniqueUpToIso e').hom,
    homEquiv_comp_uniqueUpToIso_hom]

end CategoryTheory.Functor.RepresentableBy

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Yoneda.** For a functor `F : Cᵒᵖ ⥤ Type v` and an object `X`, the map
`Hom(h_X, F) → F(X)`, `τ ↦ τ_X(𝟙 X)`, is a bijection, natural in `X` and in `F`: precomposing
with `h_g` for `g : X' ⟶ X` corresponds to `F(g)`, and postcomposing with `η : F ⟶ F'`
corresponds to `η_X`. -/
theorem bijective_yoneda_app_id {X : C} {F : Cᵒᵖ ⥤ Type v} :
    Function.Bijective (fun τ : yoneda.obj X ⟶ F ↦ τ.app (Opposite.op X) (𝟙 X)) ∧
      (∀ {X' : C} (g : X' ⟶ X) (τ : yoneda.obj X ⟶ F),
        (yoneda.map g ≫ τ).app (Opposite.op X') (𝟙 X') =
          F.map g.op (τ.app (Opposite.op X) (𝟙 X))) ∧
      ∀ {F' : Cᵒᵖ ⥤ Type v} (τ : yoneda.obj X ⟶ F) (η : F ⟶ F'),
        (τ ≫ η).app (Opposite.op X) (𝟙 X) =
          η.app (Opposite.op X) (τ.app (Opposite.op X) (𝟙 X)) :=
  ⟨yonedaEquiv.bijective, fun g τ ↦ (yonedaEquiv_naturality τ g).symm,
    fun τ η ↦ yonedaEquiv_comp τ η⟩

end CategoryTheory

namespace CategoryTheory.Functor

/-- **Representable functors.** A presheaf `F : Cᵒᵖ ⥤ Type v` is representable
(`CategoryTheory.Functor.IsRepresentable`) if and only if it is isomorphic to the functor of
points `h_P = yoneda.obj P = Hom(-, P)` of some object `P`. -/
theorem isRepresentable_iff_exists_nonempty_iso {C : Type u} [Category.{v} C]
    (F : Cᵒᵖ ⥤ Type v) : F.IsRepresentable ↔ ∃ P : C, Nonempty (yoneda.obj P ≅ F) :=
  ⟨fun _ ↦ ⟨F.reprX, ⟨F.reprW⟩⟩, fun ⟨_, ⟨e⟩⟩ ↦ IsRepresentable.mk' e⟩

end CategoryTheory.Functor

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D] {F : C ⥤ D}

/-- For a fully faithful functor `F`, the functor `T ↦ Hom(F T, F A)` is `T ↦ Hom(T, A)`. -/
noncomputable def opCompYonedaObjIso (hF : F.FullyFaithful) (A : C) :
    F.op ⋙ yoneda.obj (F.obj A) ≅ yoneda.obj A :=
  NatIso.ofComponents (fun _ ↦ hF.homEquiv.symm.toIso)
    (fun g ↦ by ext x; exact hF.map_injective (by simp))

end CategoryTheory.Functor.FullyFaithful
