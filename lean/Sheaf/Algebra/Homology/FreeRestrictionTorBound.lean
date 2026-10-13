/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Tor bounds for restricted free modules

Source: Stacks Project, Tags 066H, 066K and 0655.
(blueprint: lem-pc-free-restriction-tor-bound).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A free B-module inherits the Tor bound of the restricted regular B-module.

Source: Stacks Project, Tags 066H, 066K and 0655.
(blueprint: lem-pc-free-restriction-tor-bound).

Proof: restricted finitely supported B-valued functions on I are the direct sum,
indexed by I, of restricted copies of B. Use the natural symmetry of Tor to
resolve the test module M instead of the first argument. Tensoring that resolution
with the direct sum commutes with the sum in each degree. Direct sums of modules
are exact, so homology commutes with this sum. Its degree-j homology is therefore
the direct sum of Tor_j(B,M), zero by hypothesis. Transport back through
Tor symmetry. Empty and infinite index sets are both allowed; no finite generation
is needed. For the zero ring all terms are zero, including j=0. -/
theorem free_restriction_tor_isZero
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (I : Type u) (M : ModuleCat.{u} A) (j : ℕ)
    (hTor :
      IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((restrictScalars ρ).obj (of B B))).obj M)) :
    IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((restrictScalars ρ).obj ((free B).obj I))).obj M) := by sorry

end ModuleCat
