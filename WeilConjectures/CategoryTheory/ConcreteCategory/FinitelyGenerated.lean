/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finitely generated objects of a concrete category

An object `M` of a concrete category is *finitely generated*
(`CategoryTheory.ConcreteCategory.IsFinitelyGenerated`) if some finite set of its elements lies
in no proper subobject: every monomorphism `N ⟶ M` whose range contains the set is an
isomorphism. This is the notion of finite generation of the stalks of a constructible sheaf, for
any concrete coefficient category:

- for modules over a ring `R` it is finite generation, `Module.Finite R M`
  (`ModuleCat.isFinitelyGenerated_iff`), equivalently the existence of an epimorphism
  `R^n ⟶ M` from a finite free module (`ModuleCat.isFinitelyGenerated_iff_exists_epi`); over a
  finite ring it is finiteness of `M`
  (`ModuleCat.finite_of_isFinitelyGenerated`);
- for types it is finiteness (`CategoryTheory.ConcreteCategory.isFinitelyGenerated_iff_finite`).

Finitely generated objects are stable under isomorphisms
(`CategoryTheory.ConcreteCategory.IsFinitelyGenerated.of_iso`) and contain the zero objects
(`CategoryTheory.ConcreteCategory.isFinitelyGenerated_of_isZero`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.ConcreteCategory

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]

/-- An object `M` of a concrete category is *finitely generated* if some finite set of elements
of `M` lies in no proper subobject of `M`: every monomorphism into `M` whose range contains the
set is an isomorphism. For modules this is finite generation (`ModuleCat.isFinitelyGenerated_iff`),
for types it is finiteness (`CategoryTheory.ConcreteCategory.isFinitelyGenerated_iff_finite`). -/
def IsFinitelyGenerated (M : C) : Prop :=
  ∃ s : Set (ToType M), s.Finite ∧
    ∀ ⦃N : C⦄ (m : N ⟶ M), Mono m → s ⊆ Set.range (ConcreteCategory.hom m) → IsIso m

/-- Finite generation is invariant under isomorphism. -/
lemma IsFinitelyGenerated.of_iso {M N : C} (e : M ≅ N) (hM : IsFinitelyGenerated M) :
    IsFinitelyGenerated N := by
  obtain ⟨s, hs, h⟩ := hM
  refine ⟨ConcreteCategory.hom e.hom '' s, hs.image _, fun P m hm hsm ↦ ?_⟩
  have : IsIso (m ≫ e.inv) := h _ inferInstance fun x hx ↦ by
    obtain ⟨p, hp⟩ := hsm ⟨x, hx, rfl⟩
    exact ⟨p, by rw [ConcreteCategory.comp_apply, hp, Iso.hom_inv_id_apply]⟩
  exact IsIso.of_isIso_comp_right m e.inv

/-- Finite generation is invariant under isomorphism. -/
lemma isFinitelyGenerated_iff_of_iso {M N : C} (e : M ≅ N) :
    IsFinitelyGenerated M ↔ IsFinitelyGenerated N :=
  ⟨IsFinitelyGenerated.of_iso e, IsFinitelyGenerated.of_iso e.symm⟩

/-- A zero object is finitely generated, by the empty set: a monomorphism into a zero object is
an isomorphism. -/
lemma isFinitelyGenerated_of_isZero [HasZeroMorphisms C] {M : C} (hM : IsZero M) :
    IsFinitelyGenerated M := by
  refine ⟨∅, Set.finite_empty, fun N m _ _ ↦ ?_⟩
  have hN : IsZero N := IsZero.of_mono m hM
  exact ⟨⟨hM.to_ N, hN.eq_of_src _ _, hM.eq_of_src _ _⟩⟩

end CategoryTheory.ConcreteCategory

namespace CategoryTheory

/-- A type is finitely generated, as an object of the concrete category of types, if and only if
it is finite. -/
lemma ConcreteCategory.isFinitelyGenerated_iff_finite (M : Type u) :
    IsFinitelyGenerated (CC := fun X ↦ X) M ↔ Finite M := by
  constructor
  · rintro ⟨s, hs, h⟩
    have hm : Mono (↾(Subtype.val : s → M)) :=
      (mono_iff_injective _).2 Subtype.val_injective
    have hi : IsIso (↾(Subtype.val : s → M)) := h _ hm fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
    have : Finite s := hs.to_subtype
    exact Finite.of_surjective _ ((isIso_iff_bijective (↾(Subtype.val : s → M))).1 hi).2
  · intro _
    refine ⟨Set.univ, Set.finite_univ, fun N m hm hsm ↦ ?_⟩
    exact (isIso_iff_bijective m).2 ⟨(mono_iff_injective m).1 hm,
      fun x ↦ hsm (Set.mem_univ x)⟩

end CategoryTheory

namespace ModuleCat

open CategoryTheory.ConcreteCategory

variable {R : Type u} [Ring R]

/-- A module is finitely generated, as an object of the concrete category of modules, if and only
if it is a finitely generated module: a monomorphism of modules is an injective linear map, and
its range is a submodule, which contains a set if and only if it contains its span. -/
lemma isFinitelyGenerated_iff (M : ModuleCat.{v} R) :
    IsFinitelyGenerated M ↔ Module.Finite R M := by
  constructor
  · rintro ⟨s, hs, h⟩
    have hm : Mono (ModuleCat.ofHom (Submodule.span R s).subtype) :=
      (ModuleCat.mono_iff_injective _).2 (Submodule.subtype_injective _)
    have : IsIso (ModuleCat.ofHom (Submodule.span R s).subtype) :=
      h _ hm fun x hx ↦ ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
    have hsurj := ((ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (Submodule.span R s).subtype)).1 this).2
    refine ⟨⟨hs.toFinset, eq_top_iff.2 fun x _ ↦ ?_⟩⟩
    obtain ⟨y, rfl⟩ := hsurj x
    simp
  · intro hM
    obtain ⟨S, hS⟩ := hM.fg_top
    refine ⟨S, S.finite_toSet, fun N m hm hsm ↦ ?_⟩
    refine (ConcreteCategory.isIso_iff_bijective m).2 ⟨(ModuleCat.mono_iff_injective m).1 hm,
      fun x ↦ ?_⟩
    have hle : Submodule.span R (S : Set M) ≤ LinearMap.range m.hom :=
      Submodule.span_le.2 fun y hy ↦ hsm hy
    rw [hS] at hle
    exact hle Submodule.mem_top

/-- Over a finite ring, finitely generated modules are finite. -/
lemma finite_of_isFinitelyGenerated [Finite R] {M : ModuleCat.{v} R}
    (h : IsFinitelyGenerated M) : Finite M :=
  have := (isFinitelyGenerated_iff M).1 h
  Module.finite_of_finite R

/-- **Finite generation as an epimorphism from a finite free module.** A module `M` is finitely
generated, as an object of the concrete category of modules, if and only if there is an
epimorphism `R^n ⟶ M` from a finite free module. This is the form in which finite generation can
be stated without reference to elements, see
`AlgebraicGeometry.Scheme.isFiniteSheaf_iff_exists_epi`. -/
lemma isFinitelyGenerated_iff_exists_epi (M : ModuleCat.{u} R) :
    IsFinitelyGenerated M ↔
      ∃ (n : ℕ) (f : ModuleCat.of R (Fin n → R) ⟶ M), Epi f := by
  rw [isFinitelyGenerated_iff]
  constructor
  · intro _
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    exact ⟨n, ModuleCat.ofHom f, (ModuleCat.epi_iff_surjective _).2 hf⟩
  · rintro ⟨n, f, hf⟩
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).1 hf)

end ModuleCat
