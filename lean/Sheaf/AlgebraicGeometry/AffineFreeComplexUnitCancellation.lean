/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Homology.UnitEntrySplits

/-! # Cancelling a unit coefficient in an affine free cochain complex

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`).
(blueprint: lem-pc-affine-free-complex-unit-cancellation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A unit coefficient removes a contractible summand, with explicit complementary sizes.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`).
(blueprint: lem-pc-affine-free-complex-unit-cancellation)

Proof: Identify each free sheaf with tilde of the free module on its indicated finite
basis, using tildeFinsupp. Full faithfulness of tilde lifts the conjugated differentials
and their square-zero equations to a module complex. The global-sections isomorphism
identifies the displayed coefficient with its module coefficient and preserves units.
Reverse degree j to -j, reindex the ULift bases by Fin, and apply
ChainComplex.exists_splitting_of_isUnit_entry at -i. Its complement has sizes n(i)-1
and n(i+1)-1 at the two changed degrees, and the original sizes elsewhere. In the
identity summand the reverse differential is the contracting homotopy: it is the
inverse differential between the two nonzero terms, and zero elsewhere. The complex
relations make its homotopy identity hold in all degrees. Projection to the complement
and inclusion back are inverse up to this contraction. Apply the additive tilde functor
to these maps and the homotopy, and reverse the grading back. In unchanged degrees
the identity summand is zero, so the termwise splitting gives P'.X j ≅ P.X j.
This argument needs neither a local ring nor a residue differential nor support bounds. -/
theorem exists_affine_free_complex_unit_cancellation (R : CommRingCat.{u})
    (P : CochainComplex (Spec R).Modules ℤ) (n : ℤ → ℕ)
    (e : ∀ j : ℤ, P.X j ≅ SheafOfModules.free
      (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin (n j))))
    (i : ℤ) (p : ULift.{u} (Fin (n i))) (q : ULift.{u} (Fin (n (i + 1))))
    (hunit : IsUnit (freeMatrix ((e i).inv ≫ P.d i (i + 1) ≫ (e (i + 1)).hom) q p)) :
    ∃ P' : CochainComplex (Spec R).Modules ℤ,
      Nonempty (HomotopyEquiv P P') ∧
      (∀ j : ℤ, Nonempty (P'.X j ≅ SheafOfModules.free
        (R := (Spec R).ringCatSheaf)
        (ULift.{u} (Fin (if j = i ∨ j = i + 1 then n j - 1 else n j))))) ∧
      (∀ j : ℤ, j ≠ i → j ≠ i + 1 → Nonempty (P'.X j ≅ P.X j)) := by sorry

end AlgebraicGeometry.Scheme.Modules
