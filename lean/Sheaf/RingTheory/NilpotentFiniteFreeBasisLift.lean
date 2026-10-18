/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps

/-! # Lifting a finite basis across a nilpotent quotient

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Module

namespace ModuleCat

/-- Lift prescribed coordinates across a nilpotent reduction of a finite-free module.
Source: Stacks Project, Tag 0CQF, compatible-basis argument in the proof
(blueprint: lem-weil-pbc-nilpotent-finite-free-basis-lift).

Proof: Lift each prescribed basis vector through u. The resulting map R^r to M reduces
to an isomorphism by the adjunction equation for theta. Choose any finite basis of M
and lift the matrix of the inverse reduced map. Both products of these rectangular
matrices are square and differ from the identity by matrices with entries in ker phi.
If that ideal has exponent d, the dth power of each error matrix is zero. Finite
geometric sums invert both products, so the lifted basis map has a left inverse and
a right inverse. These coincide. Its inverse gives the desired coordinates. Equality
after reduction on the chosen basis vectors extends to all vectors by semilinearity.
The argument includes the empty basis and the zero ring and uses neither localness nor
an invariant basis number argument. -/
theorem exists_nilpotent_finiteFree_basis_lift
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hsurj : Function.Surjective φ)
    (hnil : IsNilpotent (RingHom.ker φ))
    (M : ModuleCat.{max u v} R) (N : ModuleCat.{max u v} S)
    [Module.Free R M] [Module.Finite R M]
    (u : M ⟶ (restrictScalars φ).obj N)
    (θ : (extendScalars φ).obj M ≅ N)
    (hu : Function.Surjective u)
    (hθ : (extendRestrictScalarsAdj φ).homEquiv M N θ.hom = u)
    (r : ℕ) (e : N ≃ₗ[S] (Fin r → S)) :
    ∃ e' : M ≃ₗ[R] (Fin r → R),
      ∀ (x : M) j, e (u x) j = φ (e' x j) := by
  sorry

end ModuleCat
