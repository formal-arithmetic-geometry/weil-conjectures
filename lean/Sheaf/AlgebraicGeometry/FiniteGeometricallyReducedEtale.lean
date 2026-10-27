/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields

/-!
# Finite geometrically reduced schemes over fields are etale

Source: Stacks Project, Morphisms, Tag 02GL, `lemma-etale-over-field`, and
Algebra, Tag 030W, `lemma-characterize-separable-field-extensions`.
(blueprint: lem-sfb-finite-georeduced-etale)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite geometrically reduced scheme over a field is etale over that field.
The source may be empty, and the base field need not be perfect.

Source: Stacks Project, Morphisms, Tag 02GL, `lemma-etale-over-field`, combined
with Algebra, Tag 030W, `lemma-characterize-separable-field-extensions`.
(blueprint: lem-sfb-finite-georeduced-etale)

Proof:
1. By def-weil-finite-integral-morphism, write T = Spec A with A finite-dimensional
   over k. Geometric reducedness applied to k itself makes T reduced; by
   def-pc-reduced-scheme, A is reduced. The lemma
   lem-weil-pbc-finite-dim-algebra-artinian makes A Artinian.
2. Apply lem-sfb-reduced-artinian-residue-product to decompose A canonically as
   the product of its finitely many residue fields K_i. The component maps are
   the quotient maps, so this is a k-algebra isomorphism. By
   lem-weil-pbc-spec-finite-product-fields, the spectra of these projections are
   pairwise disjoint open singletons covering T. Gluing gives an isomorphism
   T = coproduct Spec K_i over k, with inverse defined on the open summands.
3. Each K_i is finite-dimensional over k since a finite basis of A spans its
   quotient. Its structure map from k is injective: its kernel is a proper
   ideal of a field. Thus K_i/k is a finite field extension.
4. Choose an algebraic closure kbar by def-weil-algebraic-closure. The lemma
   lem-sbc-finite-affine-tensor-base-change identifies T_kbar with the coproduct
   of Spec (K_i tensor_k kbar). Geometric reducedness makes T_kbar reduced;
   reducedness on each open summand makes every K_i tensor_k kbar reduced.
   Apply lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable.
   For each finite algebraic K_i/k, its empty transcendence basis identifies
   the resulting separability notion of def-weil-pbc-separable-field-extension
   with algebraic separability.
5. Apply lem-exc-etale-coproduct-etale to these finite separable extensions and
   transport etaleness across the k-isomorphism. For A = 0 the maximal-ideal
   set and coproduct are empty, which the coproduct lemma allows. No step
   assumes that k is perfect. -/
theorem etale_of_isFinite_of_geometricallyReduced
    (k : Type u) [Field k] (T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [GeometricallyReduced f] : Etale f := by
  sorry

end AlgebraicGeometry
