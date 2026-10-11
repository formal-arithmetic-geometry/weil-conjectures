/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Flatness characterized by first Tor with ideal quotients

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00M5
(blueprint: lem-weil-pbc-flat-tor-ideal-criterion).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/--
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00M5
(blueprint: lem-weil-pbc-flat-tor-ideal-criterion).
The proof uses the first-variable Tor exact sequence, Tor symmetry, and the
finitely generated ideal criterion for flatness, as detailed in the node proof.
-/
theorem flat_iff_tor_one_quotient_ideal
    (R : Type u) [CommRing R]
    (C : Type u) [AddCommGroup C] [Module R C] :
    Module.Flat R C ↔
      ∀ I : Ideal R,
        IsZero (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R C)).obj
          (ModuleCat.of R (R ⧸ I))) := by
  sorry

end CategoryTheory
