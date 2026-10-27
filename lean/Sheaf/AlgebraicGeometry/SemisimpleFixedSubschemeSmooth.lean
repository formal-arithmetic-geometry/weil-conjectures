/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.SemisimpleCyclicClosureLinearlyReductive

/-! # Smooth fixed subschemes of semisimple elements

Source: Milne, Algebraic Groups (2017), Corollary 13.8, printed p.257,
smoothness assertion, via Theorem 13.7, printed p.256
(blueprint: lem-sfb-semisimple-fixed-subscheme-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The closed fixed subscheme of a semisimple rational point is smooth.
The internal action `ModObj H X` consists of the action morphism with its unit and
associativity laws. The closed immersion and `hfixed` specify the equalizer on every
commutative k-algebra, including nonreduced algebras. There is no connectedness
assumption on X or on the fixed subscheme.

Source: Milne, Algebraic Groups (2017), Corollary 13.8, printed p.257,
smoothness assertion (blueprint: lem-sfb-semisimple-fixed-subscheme-smooth).

Proof:
1. Let Gamma be the integer powers of s and G its reduced Zariski closure in H.
   By lem-sfb-semisimple-cyclic-closure-linearly-reductive, G is a smooth affine
   finite-type closed subgroup, is linearly reductive, and Gamma is dense in G.
   Restrict the action along its inclusion in H; both action laws restrict.
2. Over each commutative k-algebra A, a point fixed by s_A is fixed by all
   nonnegative powers by induction. Applying s_A inverse to its fixedness
   equality gives fixedness by the inverse and hence every integer power.
   The converse uses the first power. Thus hfixed identifies F with the
   common-fixed-point functor of Gamma, including on nonreduced algebras.
3. Apply lem-sfb-linearly-reductive-dense-fixed-smooth to G, Gamma, the restricted
   action on X, and the specified closed subscheme F. Its hypotheses follow
   from steps 1 and 2; its conclusion is Smooth F.hom. It allows disconnected X
   and the empty fixed subscheme. -/
theorem semisimple_fixed_subscheme_smooth
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [Smooth H.hom] [ConnectedSpace H.left]
    (X : Over (Spec (.of k))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Smooth X.hom]
    [action : ModObj H X]
    (s : StandardGroupSchemes.affine k k ⟶ H) (hs : IsSemisimpleGroupSchemePoint H s)
    (F : Over (Spec (.of k))) (i : F ⟶ X) [IsClosedImmersion i.left]
    (hfixed : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : StandardGroupSchemes.affine k A ⟶ X),
      (∃ z : StandardGroupSchemes.affine k A ⟶ F, z ≫ i = x) ↔
        (StandardGroupSchemes.map k (Algebra.ofId k A) ≫ s) • x = x) :
    Smooth F.hom := by
  sorry

end AlgebraicGeometry
