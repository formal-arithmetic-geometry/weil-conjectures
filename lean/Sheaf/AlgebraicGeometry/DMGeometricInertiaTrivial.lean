/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Trivial geometric stabilizers of a Deligne--Mumford stack

Source: Stacks Project, Tags 045H and 04SZ, with Tags 06N3, 06MB, 05W1 and 0BH4
(blueprint: lem-sfb-dm-geometric-inertia-trivial).

The equivalence is over the category of all schemes over the base. The final clause
retains nonreduced test schemes and expresses triviality inside the actual fibre category.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- A Deligne--Mumford stack with trivial geometric stabilizers is an algebraic space,
and its objects have only identity automorphisms on every test scheme.
Source: Stacks Project, Tags 045H and 04SZ; the geometric-to-arbitrary-base step
uses the unramified DM diagonal (06N3, 06MB) and its open diagonal (05W1).
(blueprint: lem-sfb-dm-geometric-inertia-trivial).

Proof:
1. For an object `x` over an arbitrary `T`, apply
   `lem-sfb-dm-isom-space-unramified` to `(x,x)`. Its automorphism space `A` is
   unramified over `T`; an automorphism and the identity give sections `a,e : T → A`.
2. By `lem-sfb-unramified-space-open-diagonal`, the equalizer of `a,e` is an open
   subscheme `W` of `T`. A map factors through `W` exactly when the restricted arrows
   agree, with their full scheme structures retained.
3. At every point of `T`, choose an algebraic closure of its residue field
   (`def-weil-algebraic-closure`, `def-weil-geometric-point`). The geometric hypothesis
   makes the restricted automorphism the identity, so every point lies in `W`.
   An open immersion with this underlying open set is an isomorphism
   (`def-weil-open-immersion`). Thus the original automorphism is the identity,
   including for nonreduced and empty `T`.
4. Form the presheaf of isomorphism classes. Two parallel fibre arrows agree because
   their quotient is an automorphism. Hence matching classes on an etale cover have
   unique overlap isomorphisms, which satisfy the cocycle condition. Stack descent
   gives effective and unique gluing. This is an etale sheaf, and the canonical
   functor from each fibre to its discrete set of classes is fully faithful and
   essentially surjective, naturally in the test scheme
   (`def-sfb-stable-pointed-moduli-groupoids`, Stacks 045H).
5. Transfer a surjective etale scheme atlas along this equivalence. For any test
   object, equality of its class with an atlas object's class is witnessed by a
   unique isomorphism. Thus the ordinary sheaf fibre product equals the stack
   2-fibre product, compatibly with restriction; its projection is surjective etale.
6. Apply `lem-sfb-etale-sheaf-space-atlas-bootstrap` to obtain an algebraic space
   in the fppf convention of `def-trf-algebraic-space`. Composing the identification
   with the equivalence of step 4 gives the equivalence over `Sch/S` asserted below.
   Step 3 already proves the last clause for every test scheme. -/
theorem dm_geometric_inertia_trivial {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsDeligneMumfordModuliStack F)
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ S)
      (x : Functor.Fiber F.p (Over.mk a)) (α : x ⟶ x), α = 𝟙 x) :
    (∃ (E : AlgebraicSpace S) (e : BasedFunctor (discreteModuli E.obj.obj) F),
      e.toFunctor.IsEquivalence) ∧
    (∀ (T : Over S) (x : Functor.Fiber F.p T) (α : x ⟶ x), α = 𝟙 x) := by
  sorry

end AlgebraicGeometry
