/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Finite projective summands inherit Tor acyclicity

Source: Stacks Project, `perfect.tex`, Tag 08IB, `lemma-compare-base-change`
(blueprint: lem-pc-finite-projective-tor-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/--
Source: Stacks Project, `perfect.tex`, Tag 08IB, `lemma-compare-base-change`.
The Tor groups here are Mathlib's `CategoryTheory.Tor'` in `ModuleCat R`, deriving
tensor product in its first variable, as recorded by `def-weil-pbc-tor-modules`.

Step 1. For each `i > 0`, take the direct sum of `m` copies of a projective
resolution of `A`. This is a projective resolution of `Fin m → A`. Tensor product
with `B` and homology commute with finite direct sums, so its `i`th Tor module is
the direct sum of `m` copies of `Tor_i^R(A, B)`, and is zero by `hTor`.

Step 2. Restrict the `A`-linear split maps `s` and `r` to `R`-linear maps. By
functoriality of Tor in its first variable (`def-weil-pbc-tor-modules`), their
images have composite the identity of `Tor_i^R(P, B)`. This module is therefore
a retract of the zero module from Step 1, so is itself zero for every `i > 0`.
(blueprint: lem-pc-finite-projective-tor-acyclic).
-/
theorem finiteProjective_tor_acyclic
    {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {B : Type u} [CommRing B] [Algebra R B]
    {P : Type u} [AddCommGroup P] [Module A P]
    (hTor : ∀ (i : ℕ), 0 < i →
      IsZero (((Tor' (ModuleCat R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (m : ℕ)
    (s : P →ₗ[A] (Fin m → A))
    (r : (Fin m → A) →ₗ[A] P)
    (hsplit : r.comp s = LinearMap.id) :
    ∀ (i : ℕ), 0 < i →
      IsZero (((Tor' (ModuleCat R) i).obj
          (@ModuleCat.of R _ P inferInstance
            (Module.compHom P (algebraMap R A)))).obj
        (ModuleCat.of R B)) := by
  sorry

end CategoryTheory
