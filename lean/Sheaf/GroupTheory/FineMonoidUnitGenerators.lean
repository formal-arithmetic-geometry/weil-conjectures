/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup

import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Torsion

/-!
# Unit generators of a fine commutative monoid

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.3 and 3.1.11,
printed pp. 98, 100; agent algebraic refinement of the unit-generating-sublist argument
(blueprint: lem-trf-fine-monoid-unit-generators).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.FineFan

/-- The unit members of a finite monoid generating list generate all units. The notation is
multiplicative, as in `IsFine`: products, powers, and `1` represent sums, natural multiples,
and `0`. The set of unit indices is `{i | IsUnit (a i)}`. The canonical unit group `Pˣ`
identifies with the units inside `Algebra.GrothendieckGroup P` by the injection in `hP`.

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.3 and 3.1.11,
printed pp. 98, 100; agent algebraic refinement, not a verbatim assertion of ILO
(blueprint: lem-trf-fine-monoid-unit-generators).

Proof:
1. By def-trf-fine-fan-blowup, the canonical map to the completion of
   def-trf-fs-log-blowup is injective. Identify `P` with its image. Its units are exactly
   those elements whose inverses also belong to `P`, and they form an abelian subgroup.
   Indeed inverse equations in the completion reflect to `P` through the injection.
2. Given `u = ∏ j, a j ^ n j` and `0 < n i`, write `n i = m + 1`. Splitting off one
   occurrence gives `a i * b = u` with `b` in `P`. Then `b * u⁻¹` belongs to `P` and
   is an inverse of `a i`; the inverse equation again reflects from the completion.
   Thus every positive exponent has a unit generator, and nonunit indices have exponent zero.
3. The monoid span of the unit generators is contained in the units, since units are closed
   under products and contain `1`. Conversely the generating-list hypothesis expresses every
   unit as a product of powers of the generators. Step 2 removes all nonunit generators,
   so this span is exactly the units. The same finite list generates the abelian unit group.
   If the unit sublist is empty, its span is `{1}` and the group is trivial.
4. If the completion is torsion free, the equation `u ^ n = 1` for `n > 0` holds also
   after embedding the unit group in the completion. It forces its image to equal `1`;
   injectivity then gives `u = 1`. -/
theorem fine_monoid_unit_generators
    (P : Type u) [CommMonoid P] (hP : IsFine P)
    (d : ℕ) (a : Fin d → P) (ha : Submonoid.closure (Set.range a) = ⊤) :
    (∀ (u : Pˣ) (n : Fin d → ℕ), (u : P) = ∏ i, a i ^ n i →
      ∀ i : Fin d, 0 < n i → IsUnit (a i)) ∧
    Submonoid.closure (a '' {i : Fin d | IsUnit (a i)}) = IsUnit.submonoid P ∧
    Group.FG Pˣ ∧
    (IsMulTorsionFree (Algebra.GrothendieckGroup P) →
      ∀ (u : Pˣ) (n : ℕ), 0 < n → u ^ n = 1 → u = 1) := by
  classical
  have hclosure : Submonoid.closure (a '' {i : Fin d | IsUnit (a i)}) =
      IsUnit.submonoid P := by
    apply le_antisymm
    · apply Submonoid.closure_le.mpr
      rintro x ⟨i, hi, rfl⟩
      exact hi
    · intro x hx
      have hxgen : x ∈ Submonoid.closure (Set.range a) := by rw [ha]; trivial
      induction hxgen using Submonoid.closure_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submonoid.subset_closure ⟨i, hx, rfl⟩
      | one => exact Submonoid.one_mem _
      | mul y z hy hz ihy ihz =>
        obtain ⟨hyunit, hzunit⟩ := (Commute.all y z).isUnit_mul_iff.mp hx
        exact Submonoid.mul_mem _ (ihy hyunit) (ihz hzunit)
  refine ⟨?_, hclosure, ?_, ?_⟩
  · intro u n hu i hi
    apply (isUnit_pow_iff (Nat.ne_of_gt hi)).mp
    exact IsUnit.prod_univ_iff.mp (hu ▸ u.isUnit) i
  · have hfg : (IsUnit.submonoid P).FG :=
      (Submonoid.fg_iff _).mpr ⟨a '' {i : Fin d | IsUnit (a i)}, hclosure,
        (Set.toFinite _).image a⟩
    have hmap : (⊤ : Submonoid Pˣ).map (Units.coeHom P) = IsUnit.submonoid P := by
      ext x
      constructor
      · rintro ⟨u, _, rfl⟩
        exact u.isUnit
      · rintro ⟨u, rfl⟩
        exact ⟨u, trivial, rfl⟩
    apply Group.fg_iff_monoid_fg.mpr
    exact ⟨Submonoid.FG.map_injective (Units.coeHom P) Units.val_injective
      (hmap.symm ▸ hfg)⟩
  · intro htf u n hn hu
    apply Units.ext
    apply hP.2
    change Algebra.GrothendieckGroup.of (u : P) = Algebra.GrothendieckGroup.of (1 : P)
    rw [map_one]
    apply (pow_eq_one_iff_left (Nat.ne_of_gt hn)).mp
    rw [← map_pow]
    have hval : (u : P) ^ n = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun v : Pˣ ↦ (v : P)) hu
    rw [hval, map_one]

end AlgebraicGeometry.FineFan
