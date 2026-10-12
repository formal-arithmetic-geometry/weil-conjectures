/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
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
      (Abelian.Ext.mk₀ f) (add_zero q) = I.extMk (L.map a ≫ e.f q) (q + 1) rfl hc := by sorry
