/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Ext universe change commutes with exact transport and composition

Source: Mathlib's Ext.homAddEquiv and Stacks Project, Tag 03FD.
-/

@[expose] public section
universe u v s t c d w
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Abelian.Ext
noncomputable section

/-- Exact-functor transport with one coefficient morphism on either side.
Keeping this construction at the level of abstract abelian categories avoids
reconstructing specialized sheaf-category data in each cohomology map. -/
@[irreducible]
def mapExactFunctorWithCoefficients
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B]
    [HasExt.{s} A] [HasExt.{s} B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {Z F : A} {W G : B} (a : W ⟶ L.obj Z) (b : L.obj F ⟶ G)
    (q : ℕ) : Ext.{s} Z F q → Ext.{s} W G q :=
  fun x ↦ ((Ext.mk₀.{s} a).comp
    (Ext.mapExactFunctor.{s, s} L x) (zero_add q)).comp
      (Ext.mk₀.{s} b) (add_zero q)

/-- Identify two Ext universes through their common derived category. -/
@[irreducible]
def universeChangeEquiv {A : Type u} [Category.{v} A] [Abelian A]
    [HasExt.{s} A] [HasExt.{t} A] (M N : A) (q : ℕ) :
    Ext.{s} M N q ≃ Ext.{t} M N q := Ext.chgUniv.{t, s}

/-- Universe change preserves the represented derived morphism.
Source: Mathlib's Ext.homAddEquiv.
(blueprint: lem-weil-pbc-ext-universe-change)

Proof: Mathlib's direct universe-change equivalence represents the same
derived morphism in either universe. -/
theorem universeChangeEquiv_hom
    {A : Type u} [Category.{v} A] [Abelian A]
    [es : HasExt.{s} A] [et : HasExt.{t} A] {M N : A} {q : ℕ}
    (x : Ext.{s} M N q) :
    let := HasDerivedCategory.standard A
    (@universeChangeEquiv A _ _ es et M N q x).hom = x.hom := by
  let := HasDerivedCategory.standard A
  unfold universeChangeEquiv
  exact Ext.homEquiv_chgUniv x

/-- Universe change preserves Yoneda composition.
Source: Mathlib's Ext.comp_hom.
(blueprint: lem-weil-pbc-ext-universe-change)

Proof: Apply the injective common derived morphism presentation and use the
formula for composition and preservation of represented morphisms. -/
theorem universeChangeEquiv_comp
    {A : Type u} [Category.{v} A] [Abelian A]
    [es : HasExt.{s} A] [et : HasExt.{t} A] {M N P : A} {a b q : ℕ}
    (x : Ext.{s} M N a) (y : Ext.{s} N P b) (h : a + b = q) :
    @universeChangeEquiv A _ _ es et M P q (x.comp y h) =
      (@universeChangeEquiv A _ _ es et M N a x).comp
        (@universeChangeEquiv A _ _ es et N P b y) h := by
  let := HasDerivedCategory.standard A
  apply Ext.homEquiv.injective
  simp only [Ext.comp_hom, universeChangeEquiv_hom]

/-- Exact functors commute with changing the Ext universe.
Source: Mathlib's Ext.mapExactFunctor_hom.
(blueprint: lem-weil-pbc-ext-universe-change)

Proof: Compute both represented morphisms in the same derived categories.
The derived functor formula is independent of the Ext universes, and universe
change preserves the represented morphism. Injectivity proves the equality. -/
theorem universeChangeEquiv_mapExactFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B]
    [esA : HasExt.{s} A] [etA : HasExt.{t} A]
    [esB : HasExt.{s} B] [etB : HasExt.{t} B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {M N : A} {q : ℕ} (x : Ext.{s} M N q) :
    @universeChangeEquiv B _ _ esB etB _ _ q
        (Ext.mapExactFunctor.{s, s, u, c, v, d} L x) =
      Ext.mapExactFunctor.{t, t, u, c, v, d} L
        (@universeChangeEquiv A _ _ esA etA _ _ q x) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  apply Ext.homEquiv.injective
  simp only [universeChangeEquiv_hom, Ext.mapExactFunctor_hom]

/-- Universe change preserves the degree-zero class of a morphism.
Source: Mathlib's Ext.mk₀_hom.
(blueprint: lem-weil-pbc-ext-universe-change)

Proof: Both classes represent the same derived morphism of degree zero. -/
theorem universeChangeEquiv_mk₀
    {A : Type u} [Category.{v} A] [Abelian A]
    [es : HasExt.{s} A] [et : HasExt.{t} A] {M N : A} (f : M ⟶ N) :
    @universeChangeEquiv A _ _ es et M N 0 (Ext.mk₀ f) = Ext.mk₀ f := by
  let := HasDerivedCategory.standard A
  apply Ext.homEquiv.injective
  simp only [universeChangeEquiv_hom, Ext.mk₀_hom]

/-- Universe change commutes with exact transport and its two coefficient morphisms.
Source: Mathlib's Ext composition and exact-functor formulas.
(blueprint: lem-weil-pbc-ext-universe-change)

Proof: Preserve the two Yoneda products and the two degree-zero classes, then
use compatibility with exact-functor transport. This proves the composite
formula with abstract abelian categories, before specializing the objects. -/
theorem universeChangeEquiv_exactComposite
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B]
    [esA : HasExt.{s} A] [etA : HasExt.{t} A]
    [esB : HasExt.{s} B] [etB : HasExt.{t} B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {Z F : A} {W G : B} (a : W ⟶ L.obj Z) (b : L.obj F ⟶ G)
    (q : ℕ) (x : Ext.{s} Z F q) :
    @universeChangeEquiv B _ _ esB etB W G q
        (((Ext.mk₀.{s} a).comp (Ext.mapExactFunctor.{s, s} L x) (zero_add q)).comp
          (Ext.mk₀.{s} b) (add_zero q)) =
      ((Ext.mk₀.{t} a).comp
        (Ext.mapExactFunctor.{t, t} L
          (@universeChangeEquiv A _ _ esA etA Z F q x)) (zero_add q)).comp
        (Ext.mk₀.{t} b) (add_zero q) := by
  simp only [universeChangeEquiv_comp, universeChangeEquiv_mk₀,
    universeChangeEquiv_mapExactFunctor]


end
end CategoryTheory.Abelian.Ext
