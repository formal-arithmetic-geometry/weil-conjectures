/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.AlgebraicGeometry.MarkedCurveDeformations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite tangent and infinitesimal automorphism spaces of curves

Source: Stacks Project, quot.tex, Tag 0D57 (lemma-curves-tangent-space), via Tag 0D1K
(blueprint: lem-sfb-curve-tangent-finiteness).

The existential structures are pinned to the square-zero deformation operations on the
actual marked isomorphism classes and actual automorphisms, rather than on replacement
vector spaces. The auxiliary base `S` only records the category of relative presheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperCurveFamily

/-- The tangent and infinitesimal automorphism spaces of a proper curve are
finite-dimensional over any field, with the usual deformation vector operations.
Source: Stacks, quot.tex, Tag 0D57, both clauses, using Tag 0D1K
(blueprint: lem-sfb-curve-tangent-finiteness).

Proof: (1) For the split square-zero extension `K ⊕ K`, the classification of flat
space deformations [lem-sfb-flat-space-split-deformation-ext] identifies the ambient
marked deformation space, with trivial deformation as origin, with Ext¹ of the naive
cotangent complex into the structure sheaf. It identifies identity-reducing trivial-family
automorphisms with Ext⁰, respecting scalar pullback, gluing addition, and composition.
(2) Forgetting properness, finite presentation and relative dimension is fully faithful
on marked deformation groupoids, hence injective on isomorphism classes. Its zero is the
trivial deformation; its infinitesimal automorphisms are exactly the same automorphisms.
(3) [lem-sfb-curve-infinitesimal-pushout] glues two curve deformations over the
special fibre to the two-direction base. Pullback by addition gives their sum, and scalar
pullback preserves curve families. The injection into ambient deformations is linear, so
its image is a subspace; the ambient Ext⁰ operations also give the automorphism module.
(4) The field is Noetherian. By [lem-sfb-space-naive-cotangent-coherent], finite
presentation gives coherent structure sheaf and coherent naive cotangent cohomology in
just degrees -1 and 0. These supply the required boundedness hypotheses.
(5) Properness and [lem-sfb-proper-space-coherent-ext-finite] imply that Ext⁰ and
Ext¹ are finite K-modules. Hence the automorphism space and the ambient deformation
space are finite-dimensional. (6) The tangent subspace is finite-dimensional: any list
longer than an ambient basis has dependent images, and injectivity pulls the relation
back. This holds over every field, and therefore also over fields of finite type over Z. -/
theorem finite_tangent_and_infinitesimalAut {S : Scheme.{u}}
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
    (X : ProperCurveFamily (Over.mk a)) :
    ∃ (tadd : AddCommGroup (Tangent X))
      (tmod : @Module K (Tangent X) _ tadd.toAddCommMonoid)
      (iadd : AddCommGroup (InfinitesimalAut X))
      (imod : @Module K (InfinitesimalAut X) _ iadd.toAddCommMonoid),
      @FiniteDimensional K (Tangent X) _ tadd tmod ∧
      @FiniteDimensional K (InfinitesimalAut X) _ iadd imod ∧
      (∀ t : Tangent X, IsTangentZero X t ↔ t = tadd.zero) ∧
      (∀ t s r : Tangent X, IsTangentAdd X t s r ↔ r = tadd.add t s) ∧
      (∀ (c : K) (t s : Tangent X), IsTangentSMul X c t s ↔ s = tmod.smul c t) ∧
      iadd.zero.val = Iso.refl _ ∧
      (∀ α β : InfinitesimalAut X, (iadd.add α β).val.hom = α.val.hom ≫ β.val.hom) ∧
      (∀ (c : K) (α β : InfinitesimalAut X),
        IsInfinitesimalAutSMul X c α β ↔ β = imod.smul c α) := by
  sorry

end AlgebraicGeometry.ProperCurveFamily
