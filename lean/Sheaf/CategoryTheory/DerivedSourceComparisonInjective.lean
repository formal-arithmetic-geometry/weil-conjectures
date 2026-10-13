/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Detecting derived classes through an acyclic source comparison

Source: Stacks Project, Tags 03FD and 015E, acyclic-resolution argument.
(blueprint: lem-sbc-derived-source-comparison-injective).
-/

@[expose] public section

universe v u₁ u₂
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory

/-- Termwise Hom comparison and acyclicity detect derived classes.
Source: Stacks Project, Tag 03FD, first and second proof paragraphs; Tag 015E.
(blueprint: lem-sbc-derived-source-comparison-injective).

Proof: Choose an injective resolution I of Y in C. Exactness of V makes V(I)
an exact resolution of V(Y). Its terms are acyclic for Hom(B,-) by hac.
Consequently Hom(B,V(I)) computes derived Hom(B,V(Y)), by the acyclic-resolution
comparison. The maps f ↦ a ≫ V(f) commute with differentials by functoriality
and associativity. Their bijectivity on injectives makes Hom(L,I) and
Hom(B,V(I)) isomorphic complexes of abelian groups. In particular their
cohomology maps are injective. The injective-resolution realization identifies
Hom(L[0],Y[0][q]) with the first cohomology group. The augmentation-compatible
acyclic-resolution realization identifies the second with
Hom(B[0],V(Y)[0][q]). Mapping a cocycle through V and precomposing by a[0]
gives precisely the displayed map: the inverse single comparison identifies
V(L[0]) with V(L)[0], and the augmentation commutes with V. Hence the displayed
map is injective before any coefficient identification. This argument also
covers degree zero and zero objects; no preservation of injectives by V is used. -/
theorem derivedSourceComparison_injective
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L)
    (hhom : ∀ (I : C), Injective I →
      Function.Bijective (fun f : L ⟶ I ↦ a ≫ V.map f))
    (hac : ∀ (I : C), Injective I →
      (preadditiveCoyoneda.obj (Opposite.op B)).rightAcyclic (V.obj I))
    (Y : C) (q : ℕ) :
    Function.Injective (fun x : (DerivedCategory.Plus.singleFunctor C 0).obj L ⟶
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y)⟦(q : ℤ)⟧ ↦
      ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
        V.mapDerivedCategoryPlus.map x) := by sorry

end CategoryTheory
