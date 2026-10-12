/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Algebra.Homology.UnitEntrySplits

/-! # Minimal finite free complexes over a scheme stalk

Source: Stacks Project, Tag 00MT, and blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-stalk-minimal-complex)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded finite free complex over a stalk has a minimal homotopy representative.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`), and blueprint
lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-stalk-minimal-complex).

Proof: Global sections on the affine scheme Spec of the stalk identify the finite
free terms and their morphisms with finite free modules and matrices over the stalk.
Reverse the integer grading. If a differential has a unit matrix entry, apply
lem-weil-pbc-free-complex-unit-entry-splits to separate a two-term identity complex.
That summand is contractible: its sole homotopy component is the inverse of its
identity differential. Projection onto the complementary complex and inclusion
therefore define a homotopy equivalence. The complement remains finite free,
with the same support bounds. Induct on the sum of ranks in degrees 0 through d;
each cancellation decreases this sum by two. When no unit entry remains, all
entries lie in the maximal ideal of the local ring, so their images under the
residue quotient are zero. Apply the associated-sheaf functor to the remaining
complex and the composed homotopies. Pullback to the residue spectrum computes
these reduced matrices. This gives the displayed vanishing of every differential.
The rank sum zero case is the zero complex, with the identity equivalence. No
cohomology hypothesis or preferred remaining rank is used in this construction. -/
theorem exists_stalk_minimal_complex {Y : Scheme.{u}} (y : Y)
    (P : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin s)))) :
    ∃ Q : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ,
      Nonempty (HomotopyEquiv P Q) ∧ Q.IsStrictlyGE 0 ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ s : ℕ, Nonempty
        (Q.X n ≅ SheafOfModules.free
          (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin s)))) ∧
      ∀ a b : ℤ,
        (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
          Q).d a b = 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
