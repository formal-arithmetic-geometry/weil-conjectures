/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.DeligneLaumon.Reduction.FormalSteps

/-!
# Degree-one Ext classes classify short exact extensions

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV; exact-functor compatibility
by Tags 0151 and 0152 (blueprint: lem-weil-pbc-ext-one-extension-classification).
-/

@[expose] public section

universe w w' t t' v v' u u'

open CategoryTheory.Limits

namespace CategoryTheory

/-- Short exact extensions with fixed endpoints are classified by their connecting class.
Source: Stacks Project, Tags 06XU and 06XV
(blueprint: lem-weil-pbc-ext-one-extension-classification).

The first clause gives every class a representative. The second says precisely that equal
classes have an isomorphism of middle objects inducing identities on both endpoints; its
reverse implication also makes the class assignment well-defined on isomorphism classes.
The third clause is compatibility with every exact additive functor. Under `Ext.homAddEquiv`,
`h.extClass` is the connecting map `h.singleδ` by `ShortExact.extClass_hom`, and
`Ext.mapExactFunctor_hom` identifies `mapExactFunctor` with the termwise derived functor,
including its single-complex and shift comparisons.

Proof plan: identify the standard heart with the original abelian category using concentration
in degree zero and full faithfulness of the single functor. Transfer short exactness across
this equivalence. The single-complex short exact sequence triangle supplies the boundary;
its naturality makes endpoint-identity isomorphisms preserve the class. Complete an arbitrary
degree-one arrow to a triangle and inverse-rotate twice. Extension closure of the standard
heart puts the middle object in the heart, so it is a single object, and the heart criterion
makes the lifted sequence short exact with the prescribed boundary. For injectivity, rotate
two triangles with equal boundaries twice and apply TR3 with identities on the common first
two objects. The third component is an isomorphism by the two-isomorphisms criterion; shift
back and lift it through the fully faithful single functor to the required middle-object
isomorphism. Finally apply the exact-functor short-exact-triangle comparison; uniqueness of
the heart boundary identifies it with the canonical boundary of the image sequence.
-/
theorem ext_one_extension_classification
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{t} C] [HasExt.{w} C] (P Q : C) :
    (∀ ξ : Abelian.Ext Q P 1,
      ∃ (B : C) (a : P ⟶ B) (b : B ⟶ Q) (z : a ≫ b = 0)
        (h : (ShortComplex.mk a b z).ShortExact), h.extClass = ξ) ∧
    (∀ (B B' : C) (a : P ⟶ B) (b : B ⟶ Q) (z : a ≫ b = 0)
      (h : (ShortComplex.mk a b z).ShortExact)
      (a' : P ⟶ B') (b' : B' ⟶ Q) (z' : a' ≫ b' = 0)
      (h' : (ShortComplex.mk a' b' z').ShortExact),
      h.extClass = h'.extClass ↔ ∃ e : B ≅ B', a ≫ e.hom = a' ∧ e.hom ≫ b' = b) ∧
    (∀ (D : Type u') [Category.{v'} D] [Abelian D]
      [HasDerivedCategory.{t'} D] [HasExt.{w'} D]
      (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (B : C) (a : P ⟶ B) (b : B ⟶ Q) (z : a ≫ b = 0)
      (h : (ShortComplex.mk a b z).ShortExact),
      h.extClass.mapExactFunctor F = (h.map_of_exact F).extClass) := sorry

end CategoryTheory
