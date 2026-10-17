/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Cohomology classes of elements in concrete abelian categories

Let `A` be an abelian category which is concrete, with additive groups as underlying types,
in which exactness and monomorphisms/epimorphisms can be tested on elements (e.g. abelian
groups or modules). For a cochain complex `K` in `A` we introduce the cohomology class
`K.cls n x hx` of a cocycle `x`, and show that every class is of this form, that two classes
agree iff the cocycles differ by a coboundary, and that classes are compatible with the maps
induced on cohomology.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A] {FA : A → A → Type*} {CA : A → Type v}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]

/-- Elementwise properties of a concrete abelian category used to compute cohomology on
elements. -/
structure ElementwiseAbelian : Prop where
  sub_apply : ∀ {X Y : A} (f g : X ⟶ Y) (x : ToType X), (f - g) x = f x - g x
  exact_of_elem : ∀ S : ShortComplex A,
    (∀ x₂ : ToType S.X₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂) → S.Exact
  elem_of_exact : ∀ S : ShortComplex A, S.Exact →
    ∀ x₂ : ToType S.X₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂
  injective_of_mono : ∀ {X Y : A} (f : X ⟶ Y) [Mono f], Function.Injective f
  surjective_of_epi : ∀ {X Y : A} (f : X ⟶ Y) [Epi f], Function.Surjective f

variable {A}

namespace ElementwiseAbelian

variable (hA : ElementwiseAbelian A)
include hA

lemma zero_apply {X Y : A} (x : ToType X) : (0 : X ⟶ Y) x = 0 := by
  have := hA.sub_apply (0 : X ⟶ Y) 0 x
  rwa [sub_zero, sub_self] at this

lemma add_apply {X Y : A} (f g : X ⟶ Y) (x : ToType X) : (f + g) x = f x + g x := by
  have h : f + g = f - (0 - g) := by abel
  rw [h, hA.sub_apply, hA.sub_apply, hA.zero_apply]
  abel

lemma neg_apply {X Y : A} (f : X ⟶ Y) (x : ToType X) : (-f) x = -f x := by
  have h : -f = 0 - f := by abel
  rw [h, hA.sub_apply, hA.zero_apply, zero_sub]

/-- Evaluation at an element as an additive map. -/
def evalHom {X Y : A} (x : ToType X) : (X ⟶ Y) →+ ToType Y where
  toFun f := f x
  map_zero' := hA.zero_apply x
  map_add' f g := hA.add_apply f g x

lemma sum_apply {X Y : A} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) (x : ToType X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  map_sum (hA.evalHom x) f s

lemma zsmul_apply {X Y : A} (c : ℤ) (f : X ⟶ Y) (x : ToType X) : (c • f) x = c • f x :=
  map_zsmul (hA.evalHom x) c f

end ElementwiseAbelian


namespace HomologicalComplex

variable (hA : ElementwiseAbelian A) {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex A c)

/-- `y` is the cohomology class of the cocycle `x`. -/
def IsCls (i : ι) [K.HasHomology i] (y : ToType (K.homology i)) (x : ToType (K.X i)) : Prop :=
  ∃ z : ToType (K.cycles i), K.iCycles i z = x ∧ K.homologyπ i z = y

include hA

lemma exists_cycles_elem (i j : ι) (hj : c.next i = j) (x : ToType (K.X i))
    (hx : K.d i j x = 0) : ∃ z : ToType (K.cycles i), K.iCycles i z = x := by
  have hS : (ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j hj)
  exact hA.elem_of_exact _ hS x hx

lemma exists_isCls_of_d_eq_zero (i j : ι) (hj : c.next i = j) (x : ToType (K.X i))
    (hx : K.d i j x = 0) : ∃ y, K.IsCls i y x := by
  obtain ⟨z, hz⟩ := K.exists_cycles_elem hA i j hj x hx
  exact ⟨_, z, hz, rfl⟩

lemma exists_isCls (i : ι) (y : ToType (K.homology i)) : ∃ x, K.IsCls i y x := by
  obtain ⟨z, rfl⟩ := hA.surjective_of_epi (K.homologyπ i) y
  exact ⟨_, z, rfl, rfl⟩

lemma IsCls.d_eq_zero {i : ι} (j : ι) {y : ToType (K.homology i)} {x : ToType (K.X i)}
    (h : K.IsCls i y x) : K.d i j x = 0 := by
  obtain ⟨z, rfl, -⟩ := h
  rw [← ConcreteCategory.comp_apply, K.iCycles_d]
  exact hA.zero_apply z

omit hA in
lemma IsCls.sub {i : ι} {y y' : ToType (K.homology i)} {x x' : ToType (K.X i)}
    (h : K.IsCls i y x) (h' : K.IsCls i y' x') : K.IsCls i (y - y') (x - x') := by
  obtain ⟨z, rfl, rfl⟩ := h
  obtain ⟨z', rfl, rfl⟩ := h'
  exact ⟨z - z', map_sub _ _ _, map_sub _ _ _⟩

omit hA in
lemma isCls_zero (i : ι) : K.IsCls i 0 0 := ⟨0, map_zero _, map_zero _⟩

lemma IsCls.eq_zero_iff (h i : ι) (hi : c.prev i = h) {y : ToType (K.homology i)}
    {x : ToType (K.X i)} (hyx : K.IsCls i y x) : y = 0 ↔ ∃ w, K.d h i w = x := by
  obtain ⟨z, rfl, rfl⟩ := hyx
  have hS : (ShortComplex.mk (K.toCycles h i) (K.homologyπ i)
      (K.toCycles_comp_homologyπ h i)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel h i hi)
  have hinj := hA.injective_of_mono (K.iCycles i)
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hA.elem_of_exact _ hS z hz
    refine ⟨w, ?_⟩
    rw [← hw, ← ConcreteCategory.comp_apply, K.toCycles_i]
  · rintro ⟨w, hw⟩
    have : K.toCycles h i w = z := by
      apply hinj
      rw [← ConcreteCategory.comp_apply, K.toCycles_i, hw]
    rw [← this, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]
    exact hA.zero_apply w

lemma IsCls.eq_iff (h i : ι) (hi : c.prev i = h) {y y' : ToType (K.homology i)}
    {x x' : ToType (K.X i)} (hyx : K.IsCls i y x) (hyx' : K.IsCls i y' x') :
    y = y' ↔ ∃ w, K.d h i w = x - x' := by
  rw [← sub_eq_zero]
  exact IsCls.eq_zero_iff hA K h i hi (IsCls.sub K hyx hyx')

omit hA in
lemma IsCls.map {L : HomologicalComplex A c} (φ : K ⟶ L) {i : ι} {y : ToType (K.homology i)}
    {x : ToType (K.X i)} (h : K.IsCls i y x) :
    L.IsCls i (HomologicalComplex.homologyMap φ i y) (φ.f i x) := by
  obtain ⟨z, rfl, rfl⟩ := h
  refine ⟨HomologicalComplex.cyclesMap φ i z, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  · rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]

end HomologicalComplex

end CategoryTheory
