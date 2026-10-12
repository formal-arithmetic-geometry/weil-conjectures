/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Algebra.Homology.UnitEntrySplits

/-! # One unit cancellation over a scheme stalk

Source: Stacks Project, Tag 00MT, and blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-stalk-unit-cancellation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero residue differential permits one cancellation, dropping two term ranks.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`), applied once over the
local ring of the stalk; blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-stalk-unit-cancellation).

Proof: Use the chosen finite free sheaf identifications to take global sections on
Spec of the stalk. Maps between these free sheaves are matrices over the stalk,
and pullback along its residue quotient reduces each coefficient. A nonzero
residue differential has a nonzero coefficient, whose lift is outside the maximal
ideal and hence is a unit. The complex shape and the support bounds force this
map to go from degree i to degree i+1 with 0 <= i < d. Reverse grading and apply
ChainComplex.exists_splitting_of_isUnit_entry to this coefficient, once. Its
complement has one less basis vector in each of these two degrees and the same
bases elsewhere. The identity summand has a contracting homotopy with the inverse
identity as its only nonzero component. Projection to the complement and inclusion
from it compose to the identity on the complement; their other composite differs
from the identity by that contraction. Apply the associated-sheaf functor and
reverse grading back to obtain the asserted homotopy equivalence. Outside the
original support the complement agrees with the original zero terms, since both
cancelled degrees are inside the support. The resulting bases give the displayed
free sheaf identifications. This argument performs exactly one cancellation; it
makes no assertion that the complementary complex has zero residue differentials.
If d=0 or all ranks are zero, the nonzero-differential hypothesis is impossible. -/
theorem exists_stalk_unit_cancellation {Y : Scheme.{u}} (y : Y)
    (P : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d) (n : ℤ → ℕ)
    (hfree : ∀ j : ℤ, Nonempty
      (P.X j ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin (n j)))))
    (hbad : ¬ ∀ a b : ℤ,
      (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
        P).d a b = 0) :
    ∃ (P' : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ)
      (n' : ℤ → ℕ) (i : ℕ),
      i < d ∧ Nonempty (HomotopyEquiv P P') ∧
      P'.IsStrictlyGE 0 ∧ P'.IsStrictlyLE d ∧
      (∀ j : ℤ, Nonempty
        (P'.X j ≅ SheafOfModules.free
          (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin (n' j))))) ∧
      n' (i : ℤ) + 1 = n (i : ℤ) ∧
      n' ((i : ℤ) + 1) + 1 = n ((i : ℤ) + 1) ∧
      (∀ j : ℤ, j ≠ (i : ℤ) → j ≠ (i : ℤ) + 1 → n' j = n j) := by sorry

end AlgebraicGeometry.Scheme.Modules
