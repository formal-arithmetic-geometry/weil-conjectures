/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact functors on cocycle representatives of Ext

Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
-/

@[expose] public section

universe v w w'
open CategoryTheory CochainComplex HomComplex Limits Abelian

namespace CategoryTheory.InjectiveResolution

/-- An exact functor sends the roof of a single cocycle to the roof of its image.
Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-ext-exact-functor-cocycle)

Proof: Express the Ext class of the cocycle as the derived-category roof with
right arrow the augmentation, using extEquivCohomologyClass_symm_mk_hom.
The derived functor of L takes this roof to the roof of L(a), because L is
exact and hence preserves quasi-isomorphisms. Precomposition with α changes
the numerator to α;L(a). The augmentation homotopy becomes equality in the
homotopy category and then in the derived category. Thus the image of the
augmentation followed by φ equals the target augmentation, after the canonical
single-complex comparison. Cancel the invertible target augmentation to identify
the image roof with the roof of α;L(a);φ. Apply injectivity of Ext.hom.
This calculation only concerns cocycles; it does not assert a homology square
or construct the map on quotient groups. In degree zero the same roof calculation
holds, and if a or α is zero both roofs are zero. -/
theorem ext_mapExactFunctor_cocycle
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution (L.obj B))
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B ≫ R'.ι')))
    (q : ℕ) (a : A ⟶ R.cochainComplex.X (q : ℤ))
    (ha : a ≫ R.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0)
    (ha' : (α ≫ L.map a ≫ φ.f (q : ℤ)) ≫
      R'.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    (Ext.mk₀ α).comp
      ((R.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) _ rfl ha))).mapExactFunctor L)
      (zero_add q) =
    R'.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ))
        (zero_add (q : ℤ)) _ rfl ha')) := by sorry

end CategoryTheory.InjectiveResolution
