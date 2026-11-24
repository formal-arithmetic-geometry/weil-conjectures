/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.IntGRing

/-!
# Finitely generated integer algebras are G-rings

Every finitely generated commutative ring is a G-ring.

## References

* Stacks Project, More on Algebra, Proposition 07PX, items (3) and (5), using
  Proposition 07PV.
-/

@[expose] public section

universe u

/-- Every finitely generated commutative ring, regarded as an algebra over the integers,
is a G-ring. -/
theorem isGRing_of_finiteType_int (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] :
    IsGRing R := by
  exact isGRing_of_finiteType (R := ℤ) (S := R) Int.isGRing
