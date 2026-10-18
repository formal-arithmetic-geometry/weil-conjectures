/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.RingTheory.FiniteProjectiveK0
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The determinant homomorphism on finite-projective K₀

Source: Stacks Project, More on Algebra, Tag 0AFX and the preceding determinant
construction; Tag 0B8I and the following Picard-group description
(blueprint: lem-trf-k0-determinant-map).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module.FiniteProjectiveK0

/-- A determinant homomorphism sends every finite projective module that is free of rank
one at every prime to its own Picard class, and sends the ring to the identity class.
Here a Picard class is specified by a linear isomorphism between its representative
`CommRing.Pic.AsModule` and the given module. Thus no invertibility hypothesis replaces
the explicit prime-local rank-one hypothesis. `Additive` writes tensor product additively.
Source: Stacks Project, Tag 0AFX, specialized to rank one; Tag 0B8I and the subsequent
Picard-group description (blueprint: lem-trf-k0-determinant-map).

Proof, step 1: a finite projective module is a direct summand of a finite free module.
The determinant construction and `determinantModule_finite_projective` make its determinant
finite projective, free of rank one on a finite standard cover and hence at every prime.
The determinant exact-sequence isomorphism for an isomorphism followed by zero, together
with `determinantModule_zero`, makes its Picard class invariant under isomorphism.
Applying that isomorphism to a split direct-sum sequence gives tensor multiplicativity.
Step 2: for a module Q of prime-local rank one, each nonzero free localization chart
has rank one, by further localization at a prime and invariant basis number. On a zero
chart all modules vanish. The first exterior power is Q itself, and its transition maps
are the transition maps of Q. Thus det(Q) is isomorphic to Q. In particular det(S) is S;
induction using split sequences gives det(S^n) isomorphic to S, including n = 0.
Step 3: the finite projective modules of prime-local rank one form the Picard group.
Tensor products preserve finite projectivity and localize to rank-one free modules by
the localization-tensor-product equivalence. The tensor associativity, symmetry and unit
isomorphisms give its commutative monoid law. If L has finite free complement L', then
L tensor det(L') is det(L direct-sum L'), hence S, providing its inverse. This agrees
with Mathlib's invertible-module Picard group by the tensor-inverse characterization
of Tag 0B8I; its representatives have the specified linear-isomorphism classes.
Step 4: assign to every isomorphism-class generator of the existing K₀ presentation the
Picard class of its determinant. Extend to the free abelian group. Tensor multiplicativity
kills every relation e_a + e_b - e_(a direct-sum b), so the map descends to K₀.
Step 2 gives the rank-one formula and the normalization at S. -/
theorem exists_determinantMap (S : Type u) [CommRing S] :
    ∃ det : Module.FiniteProjectiveK0 S →+ Additive (CommRing.Pic S),
      (∀ (Q : Type v) [AddCommGroup Q] [Module S Q]
        [Module.Finite S Q] [Module.Projective S Q],
        (∀ (p : Ideal S) [p.IsPrime],
          Nonempty (LocalizedModule p.primeCompl Q ≃ₗ[Localization p.primeCompl]
            Localization p.primeCompl)) →
        Nonempty (CommRing.Pic.AsModule (det (mk S Q)).toMul ≃ₗ[S] Q)) ∧
      det (mk S S) = Additive.ofMul (1 : CommRing.Pic S) := sorry

end Module.FiniteProjectiveK0
