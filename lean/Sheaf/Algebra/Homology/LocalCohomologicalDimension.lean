/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Data.ENat.Lattice
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Local cohomological dimension of an ideal

Source: Stacks Project, Local Cohomology, Definition 0DX8 and Lemma 0DX7
(blueprint: def-per-local-cohomological-dimension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- The local cohomological dimension, computed from the right derived functors of
ideal-power torsion on all small modules. The bottom element represents the integer `-1`,
nonnegative integers have their usual values, and the top element represents an unbounded
set of nonvanishing degrees. For a finitely generated ideal, this is the least integer
`q ≥ -1` for which all higher local cohomology modules vanish.
Source: Stacks Project, Definition 0DX8 and Lemma 0DX7
(blueprint: def-per-local-cohomological-dimension). -/
noncomputable def localCohomologicalDimension {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : WithBot ℕ∞ :=
  sSup {q : WithBot ℕ∞ | ∃ j : ℕ, q = j ∧
    ∃ M : ModuleCat.{u} R, ¬ IsZero (((idealPowerTorsion I).rightDerived j).obj M)}

end ModuleCat
