/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Order.Directed

/-! # Isomorphism descent from an elementwise ring-colimit criterion

Source: Stacks Project, Algebra, Tag 05N7 (2), (3).
(blueprint: lem-pc-elementwise-fp-module-equiv-descent)
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

namespace AlgebraicGeometry

/-- An isomorphism of the limit base changes of two fixed finitely presented
modules descends to one stage of a directed ring system.

Source: Stacks Project, Algebra, Tag 05N7 (2), (3).
(blueprint: lem-pc-elementwise-fp-module-equiv-descent)

Proof:
1. The representative and eventual-zero assumptions identify C as the ring
   colimit. Define the map to any other cocone on a representative g_j(a).
   Move two equal representatives to a common stage and apply eventual zero
   to their difference to prove independence of the representative. Common
   stages also prove the ring-map laws; representatives prove uniqueness.
   For a preorder, take its poset reflection and choose representatives;
   mutually comparable transitions are inverse by identity and composition.
   Lift rings, indices and modules to one common universe using ULift, so
   the categorical map-descent theorem applies, and transport back afterward.
2. Apply Tag 05N7 (2) to the isomorphism and its inverse. Move the two descended
   maps to a common stage. The canonical tensor comparisons satisfy the
   unit-tensor equations, so their extensions are the original maps.
3. The stage modules are finitely presented by base change. Each composite
   becomes the identity over C. Apply Tag 05N7 (3) to each composite and the
   appropriate identity, and take a common upper bound for the resulting
   equalities. Base change preserves composition and identities, so the two
   stage maps are inverse and define a linear equivalence. Transport back
   through the universe lifts and poset representatives. No flatness or
   finite presentation of any ring is needed. The proof also applies to zero
   rings, zero modules, and empty finite presentations.
-/
theorem exists_stage_equiv_of_elementwise_colimit
    {J : Type v} [Preorder J] [IsDirectedOrder J]
    (A : J → Type u) [∀ j, CommRing (A j)]
    (f : ∀ (j l : J), j ≤ l → A j →+* A l)
    (hself : ∀ j, f j j le_rfl = RingHom.id (A j))
    (hcomp : ∀ j l m (hjl : j ≤ l) (hlm : l ≤ m),
      (f l m hlm).comp (f j l hjl) = f j m (hjl.trans hlm))
    (C : Type w) [CommRing C] (g : ∀ j, A j →+* C)
    (hg : ∀ j l (hjl : j ≤ l), (g l).comp (f j l hjl) = g j)
    (hsurj : ∀ c : C, ∃ j a, g j a = c)
    (hzero : ∀ j a, g j a = 0 → ∃ (l : J) (hjl : j ≤ l), f j l hjl a = 0)
    (i : J) (P : Type x) (N : Type y) [AddCommMonoid P] [AddCommMonoid N]
    [Module (A i) P] [Module (A i) N]
    [Module.FinitePresentation (A i) P] [Module.FinitePresentation (A i) N]
    (e : letI : Algebra (A i) C := (g i).toAlgebra
      Nonempty (C ⊗[A i] P ≃ₗ[C] C ⊗[A i] N)) :
    ∃ (j : J) (hij : i ≤ j),
      letI : Algebra (A i) (A j) := (f i j hij).toAlgebra
      Nonempty (A j ⊗[A i] P ≃ₗ[A j] A j ⊗[A i] N) := by sorry

end AlgebraicGeometry
