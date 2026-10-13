/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact-functor transport of a resolution cocycle

Source: Stacks Project, Derived Categories, Tag 013P; Cohomology, Tag 01FB.
(blueprint: lem-weil-pbc-exact-functor-resolution-cocycle)
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private noncomputable def comparisonExtension
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] (L : C ⥤ D) [L.Additive]
    {A : C} {B : D} (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex) :
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex ⟶
      I.cochainComplex where
  f n := if hn : 0 ≤ n then
    L.map (R.cochainComplexXIso n n.toNat (Int.toNat_of_nonneg hn)).hom ≫
      e.f n.toNat ≫ (I.cochainComplexXIso n n.toNat (Int.toNat_of_nonneg hn)).inv
    else 0
  comm' n m h := by
    change n + 1 = m at h
    subst m
    by_cases hn : 0 ≤ n
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by simp]
      simp only [Int.natCast_nonneg, dite_true, Int.toNat_natCast,
        Functor.mapHomologicalComplex_obj_d]
      rw [R.cochainComplex_d _ _ k (k + 1) rfl (by simp),
        I.cochainComplex_d _ _ k (k + 1) rfl (by simp)]
      simp only [Functor.map_comp, Category.assoc,
        Iso.inv_hom_id_assoc]
      simp only [Iso.map_inv_hom_id_assoc]
      simpa only [Category.assoc, Functor.mapHomologicalComplex_obj_d] using
        congrArg (fun t ↦ L.map (R.cochainComplexXIso k k rfl).hom ≫ t ≫
          (I.cochainComplexXIso ((k + 1 : ℕ) : ℤ) (k + 1) rfl).inv)
        (e.comm k (k + 1))
    · exact (L.map_isZero (R.cochainComplex.isZero_of_isStrictlyGE 0 n (by lia))).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private lemma comparisonExtension_f
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] (L : C ⥤ D) [L.Additive]
    {A : C} {B : D} (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex)
    (q : ℕ) :
    (comparisonExtension L R I e).f q =
      L.map (R.cochainComplexXIso q q rfl).hom ≫ e.f q ≫
        (I.cochainComplexXIso q q rfl).inv := by
  simp [comparisonExtension]

/-- The derived-category morphism equality underlying exact-functor cocycle transport.

Source: Stacks Project, Derived Categories, Tag 013P; Cohomology, Tag 01FB.
(blueprint: lem-weil-pbc-exact-functor-resolution-cocycle-hom)
The proof extends the supplied comparison to integer complexes, applies the
exact-functor formula for `Ext.mapExactFunctor_hom`, and simplifies the
single-complex and shift isomorphisms. -/
theorem exactFunctor_resolution_cocycle_hom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasExt.{w₁} C] [HasExt.{w₂} D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (f : L.obj A ⟶ B)
    (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex)
    (he : L.map (R.ι.f 0) ≫ e.f 0 = f ≫ I.ι.f 0)
    {P : C} (q : ℕ) (a : P ⟶ R.cocomplex.X q)
    (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
    (hc : (L.map a ≫ e.f q) ≫ I.cocomplex.d q (q + 1) = 0) :
    (((R.extMk a (q + 1) rfl ha).mapExactFunctor L).comp
      (Abelian.Ext.mk₀ f) (add_zero q)).hom =
      (I.extMk (L.map a ≫ e.f q) (q + 1) rfl hc).hom := by sorry

/-- An augmented chain comparison computes exact-functor transport of Ext,
followed by the coefficient morphism lifted by that comparison.

Source: Stacks Project, Derived Categories, Tag 013P, lemma-morphisms-lift;
Cohomology, Tag 01FB, remark-explain-arrow.
(blueprint: lem-weil-pbc-exact-functor-resolution-cocycle)

Proof: Extend the natural-number resolutions by zero to integer cochain complexes.
The augmentation of R is a quasi-isomorphism; exactness of L preserves it.
The commutation at degree zero of e with the augmentations gives a commuting square
from the single complex on L(A) into the extended complexes. In the derived category
invert the augmentations. The resulting equality identifies the map induced by e
with the coefficient morphism f. The closed map a represents R.extMk a under the
Hom-complex computation of Ext. Applying L to that representative and then e gives
L(a) followed by e in degree q. Thus exact-functor transport followed by Ext.mk₀ f
is precisely its class in I. Extension by zero also gives this argument in degree
zero; no negative boundary is introduced, and zero objects cause no exception. -/
theorem exactFunctor_resolution_cocycle
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasExt.{w₁} C] [HasExt.{w₂} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (f : L.obj A ⟶ B)
    (R : InjectiveResolution A) (I : InjectiveResolution B)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶ I.cocomplex)
    (he : L.map (R.ι.f 0) ≫ e.f 0 = f ≫ I.ι.f 0)
    {P : C} (q : ℕ) (a : P ⟶ R.cocomplex.X q)
    (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
    (hc : (L.map a ≫ e.f q) ≫ I.cocomplex.d q (q + 1) = 0) :
    ((R.extMk a (q + 1) rfl ha).mapExactFunctor L).comp
      (Abelian.Ext.mk₀ f) (add_zero q) = I.extMk (L.map a ≫ e.f q) (q + 1) rfl hc := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  apply Abelian.Ext.ext
  exact exactFunctor_resolution_cocycle_hom L f R I e he q a ha hc
