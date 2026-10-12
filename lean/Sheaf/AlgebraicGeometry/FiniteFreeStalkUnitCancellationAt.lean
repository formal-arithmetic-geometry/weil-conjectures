/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Homology.UnitEntrySplits

/-! # Unit cancellation at a specified degree

Source: Stacks Project, Tag 00MT, and blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-stalk-unit-cancellation-at)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Cancel the specified nonzero residue differential, retaining every rank equation.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`), applied once;
blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-stalk-unit-cancellation-at)

Proof: Choose the given free-sheaf identifications. On the affine scheme Spec of
O_{Y,y}, free sheaves are the associated sheaves of their finite free modules.
Read the differential in degree i as a matrix over O_{Y,y}. The pullback free
identifications reduce its coefficients modulo the maximal ideal. The given
nonzero residue differential therefore has a nonzero matrix coefficient, whose
lift is a unit in the local ring. Reverse grading and apply
ChainComplex.exists_splitting_of_isUnit_entry to that entry. The complement
has one fewer basis vector in degrees i and i+1 and the original bases in all
other degrees. The other summand is the identity two-term complex, contracted
by the inverse of its differential in the reverse direction, with zero
components elsewhere. Projection and inclusion are inverse up to this
contraction. Apply the additive associated-sheaf functor and reverse grading
back to obtain the homotopy equivalence and free-sheaf identifications. Because
i and i+1 are both in [0,d], outside this interval the complementary terms
agree with the original zero terms, so both support bounds persist. Record the
cardinalities of the complementary bases: both affected sizes drop by exactly
one, and all other sizes stay equal. No choice of cancellation degree is part
of this statement; that is established separately from the support bounds. -/
theorem exists_stalk_unit_cancellation_at {Y : Scheme.{u}} (y : Y)
    (P : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d) (n : ℤ → ℕ)
    (hfree : ∀ j : ℤ, Nonempty
      (P.X j ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin (n j)))))
    (i : ℕ) (hi : i < d)
    (hne :
      (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
        P).d (i : ℤ) ((i : ℤ) + 1) ≠ 0) :
    ∃ (P' : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ)
      (n' : ℤ → ℕ),
      Nonempty (HomotopyEquiv P P') ∧
      P'.IsStrictlyGE 0 ∧ P'.IsStrictlyLE d ∧
      (∀ j : ℤ, Nonempty
        (P'.X j ≅ SheafOfModules.free
          (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin (n' j))))) ∧
      n' (i : ℤ) + 1 = n (i : ℤ) ∧
      n' ((i : ℤ) + 1) + 1 = n ((i : ℤ) + 1) ∧
      (∀ j : ℤ, j ≠ (i : ℤ) → j ≠ (i : ℤ) + 1 → n' j = n j) := by sorry

end AlgebraicGeometry.Scheme.Modules
