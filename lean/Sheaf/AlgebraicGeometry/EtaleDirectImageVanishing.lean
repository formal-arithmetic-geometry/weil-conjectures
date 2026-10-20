/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion

/-!
# Vanishing of higher étale direct images above twice the dimension

Source: the master blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-fullcd-etale-origin`, node `lem-sf-etale-direct-image-vanishing`, order 1790
(blueprint: lem-sf-etale-direct-image-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-
The integer-annihilation hypothesis is written explicitly so that the statement
also covers the zero coefficient ring and records invertibility in the base field.
-/
/--
For an algebraically closed field and a finite torsion coefficient ring, the higher
direct images of every étale module sheaf vanish above twice the dimension of the
source.  The conclusion is the existing all-module uniform direct-image predicate,
whose body is exactly the defining vanishing condition.

Source: master blueprint, `sec-smooth-purity/sk-prop-sf-fullcd-etale-origin`,
node `lem-sf-etale-direct-image-vanishing`, order 1790.

Proof plan:
1. Algebraic closedness gives separable closedness (`def-kun-separably-closed`).
   Finite type gives local finite type and quasi-compactness
   (`def-weil-finite-type-morphism`).  Use the structure map `f ≫ aY` on `X`,
   independently of its initially supplied map `aX`.  The positive annihilator
   of `A` shows its additive group is torsion, including for the zero ring.
2. Apply `Etale.isZero_higherDirectImage_of_two_mul_lt`
   (`lem-kun-relative-torsion-direct-image-dimension-bound`) with these structure
   maps and the given dimension bound, to every module sheaf and degree above `2d`.
   This bound has no separatedness, properness or constructibility assumption.
3. The resulting all-module vanishing is precisely
   `Etale.HasUniformDirectImageVanishingLE A f (2 * d)`
   (`def-sf-uniform-direct-image-vanishing`); it therefore gives the stated UDV
   conclusion in the global finite-field, coefficient-stage and separated setting.
(blueprint: lem-sf-etale-direct-image-vanishing)
-/
theorem etale_direct_image_vanishing_above_twice_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ IsUnit (n : k) ∧ ∀ a : A, n • a = 0) :
    Etale.HasUniformDirectImageVanishingLE A f (2 * d) := by
  obtain ⟨n, hn, -, hnA⟩ := hA
  have hAtors : IsAddTorsion A := fun a ↦
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hnA a⟩
  intro M q hq
  exact Etale.isZero_higherDirectImage_of_two_mul_lt hAtors f (f ≫ aY) aY rfl d hX M q
    (by simpa using hq)

end AlgebraicGeometry
