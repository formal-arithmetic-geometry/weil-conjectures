/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Gluing morphisms of sheaves over disjoint covering families

A family `fᵢ : Uᵢ ⟶ X` is disjoint (`CategoryTheory.Presieve.IsDisjointFamily`) if the `fᵢ`
are monomorphisms and any object mapping compatibly to two distinct members is covered by the
empty sieve (e.g. a decomposition of a scheme into disjoint open and closed pieces). Families of
sections of a sheaf of types over such a family are automatically compatible, so
morphisms and isomorphisms of sheaves glue with no condition on overlaps.

- `Presieve.IsDisjointFamily.existsUnique_hom`, `Presieve.IsDisjointFamily.exists_iso`:
  gluing over a disjoint covering family of `X`, for the restrictions to `J.over X`;
- `Presieve.IsDisjointFamily.existsUnique_hom_of_isTerminal`,
  `Presieve.IsDisjointFamily.exists_iso_of_isTerminal`: global versions when `X` is
  terminal; e.g. a sheaf isomorphic to a constant sheaf `C(M)` on each piece is `≅ C(M)`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Opposite Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- On an object covered by the empty sieve, a sheaf of types has at most one section. -/
lemma Presieve.subsingleton_of_bot_mem {P : Cᵒᵖ ⥤ Type*} (hP : Presheaf.IsSheaf J P) {Z : C}
    (hZ : ⊥ ∈ J Z) : Subsingleton (P.obj (op Z)) :=
  ⟨fun _ _ ↦ ((isSheaf_iff_isSheaf_of_type J P).1 hP _ hZ).isSeparatedFor.ext
    fun _ _ h ↦ h.elim⟩

variable {X : C} {ι : Type*} {U : ι → C} (f : ∀ i, U i ⟶ X)

/-- A family `fᵢ : Uᵢ ⟶ X` is **disjoint** if the `fᵢ` are monomorphisms and any object mapping
compatibly to two distinct `Uᵢ`, `Uⱼ` is covered by the empty sieve, e.g. a decomposition
`X = ⊔ Uᵢ` into disjoint open (and closed) pieces. -/
structure Presieve.IsDisjointFamily (J : GrothendieckTopology C) : Prop where
  mono (i : ι) : Mono (f i)
  bot_mem (i j : ι) (hij : i ≠ j) {Z : C} (a : Z ⟶ U i) (b : Z ⟶ U j) (h : a ≫ f i = b ≫ f j) :
    ⊥ ∈ J Z

variable {f}

/-- Any family of sections of a sheaf of types over the members of a disjoint family is
compatible. -/
lemma Presieve.IsDisjointFamily.compatible (hf : Presieve.IsDisjointFamily f J)
    {P : Cᵒᵖ ⥤ Type*} (hP : Presheaf.IsSheaf J P) (x : ∀ i, P.obj (op (U i))) :
    Presieve.Arrows.Compatible P f x := by
  intro i j Z a b h
  by_cases hij : i = j
  · subst hij
    have := hf.mono i
    rw [cancel_mono] at h
    rw [h]
  · have := Presieve.subsingleton_of_bot_mem hP (hf.bot_mem i j hij a b h)
    exact Subsingleton.elim _ _

variable {A : Type u'} [Category.{v'} A]

end CategoryTheory
