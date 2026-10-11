/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.RingTheory.GRing
import Mathlib.RingTheory.FiniteType

/-!
# Finitely generated integer algebras are G-rings

Source: Stacks Project, More on Algebra, Proposition 07PX, items (3) and (5),
using Proposition 07PV (blueprint: lem-weil-pbc-finite-type-z-g-ring).
-/

universe u

/-- Every finitely generated commutative ring, regarded as an algebra over the integers,
is a G-ring. Source: Stacks Project, More on Algebra, Proposition 07PX, items (3) and (5),
using Proposition 07PV (blueprint: lem-weil-pbc-finite-type-z-g-ring).

Proof:
1. The canonical map from the integers to `R` makes `R` a finite type integer algebra.
   If finitely many elements generate `R` as a ring, evaluation gives a surjection from
   the polynomial ring over the integers in those finitely many variables to `R`.
   This is precisely the hypothesis `Algebra.FiniteType ℤ R`.
2. The integers are a G-ring by Proposition 07PX (3) (`lem-weil-pbc-z-g-ring`). Apply
   finite type permanence, Proposition 07PV (`lem-weil-pbc-finite-type-over-g-ring`),
   to the canonical integer algebra structure to conclude that `R` is a G-ring. -/
theorem isGRing_of_finiteType_int (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] :
    IsGRing R := by
  sorry
