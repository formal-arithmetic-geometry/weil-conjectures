/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.FlatTorIdealCriterion
import Sheaf.CategoryTheory.OpcyclesTorSurjection

/-!
# Flatness of opcycles from exactness after tensoring

Source: Stacks Project, More on Algebra, Lemma 15.59.2 (Tag 0653), Tor argument
(blueprint: lem-pc-module-flat-opcycles-tor-criterion).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace Module.Flat

/-- (blueprint: lem-pc-module-flat-opcycles-tor-criterion) Stacks Project, More on Algebra,
Lemma 15.59.2 (Tag 0653). For a complex of flat modules, if tensoring with every module
is exact in degree `a - 1`, its degree-`a` opcycles are flat. Put
`Q = P^a / im(d^{a-1})`. The Tor argument gives a surjection from the preceding tensor
homology onto `Tor₁(Q, N)` for every `N` (lem-pc-module-opcycles-tor-surjection).
Exactness makes this Tor group zero. Apply the ideal-quotient Tor criterion
(lem-weil-pbc-flat-tor-ideal-criterion) to conclude that `Q` is flat. -/
theorem opcycles_of_exactAt {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i))
    (hexact : ∀ N : ModuleCat R,
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    Module.Flat R (P.opcycles a) := by
  sorry

end Module.Flat
