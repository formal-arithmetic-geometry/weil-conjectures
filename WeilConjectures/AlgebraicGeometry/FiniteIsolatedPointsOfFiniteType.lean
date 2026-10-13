/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType

/-!
# Finitely many isolated points of a finite type algebra over a field

Source: Stacks Project, Algebra, Lemma 10.145.3 (Tag 00UK), proof, and the
Noetherian finite-minimal-prime argument
(blueprint: lem-weil-pbc-finite-type-field-finite-isolated-points).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- A finite type algebra over a field has only finitely many points with open singleton.
Source: Stacks Project, Algebra, Lemma 10.145.3 (Tag 00UK), proof
(blueprint: lem-weil-pbc-finite-type-field-finite-isolated-points).

Proof:
1. A field is Noetherian, and a finite type algebra over it is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`.
2. The set of minimal prime ideals is finite by
   `lem-weil-pbc-noetherian-finitely-many-minimal-primes`.
3. If `{q}` is open, the basic-open basis from
   `lem-weil-pbc-spec-localization-away-basic-open` supplies `f` with `D(f) = {q}`.
   For any prime `p` contained in `q`, the fact that `f` is not in `q` implies it is
   not in `p`, so `p` lies in `D(f)` and equals `q`. Thus `q` is minimal.
4. The isolated points form a subset of the finite set of minimal primes from step 2,
   hence are finite. This includes the isolated closed points counted in Tag 00UK. -/
theorem Spec.finite_setOf_isOpen_singleton_of_finiteType
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    {q : Spec (CommRingCat.of A) | IsOpen ({q} : Set (Spec (CommRingCat.of A)))}.Finite := by
  sorry

end AlgebraicGeometry
