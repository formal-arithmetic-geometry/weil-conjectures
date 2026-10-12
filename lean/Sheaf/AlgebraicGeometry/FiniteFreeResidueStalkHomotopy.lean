/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The local-ring homotopy normal form of a finite free complex

Source: blueprint lem-pc-perfect-locus, proof step 4; Stacks Project, Tag 00MT.
(blueprint: lem-pc-finite-free-residue-stalk-homotopy)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Residue cohomology determines the homotopy normal form over the local ring.

Source: blueprint lem-pc-perfect-locus, proof step 4, and Stacks Project, Tag 00MT.
(blueprint: lem-pc-finite-free-residue-stalk-homotopy).

Proof: Choose finite bases of the terms. Pullback to Spec of the local ring gives
quasicoherent finite free terms, hence a bounded finite free complex of modules over
that ring. Its scalar extension to the residue field is the residue pullback in the
hypothesis: fromSpecResidueField factors as Spec of the residue quotient followed by
fromSpecStalk. Reverse the integer grading to use Tag 00MT. Whenever a differential
matrix has a unit entry, split off the two-term identity complex. Projecting away
that summand and including the complement are inverse up to the contraction of the
identity complex. Induct on the sum of the term ranks in degrees 0 through d; each
cancellation decreases that sum by two and preserves support. At termination every
entry belongs to the maximal ideal, so reduction has zero differentials. Its terms
are therefore its cohomology. The hypothesis makes their dimensions zero off i and
r in degree i. Dimensions of free residue modules equal their numbers of basis
vectors, so the remaining local complex is a single rank-r free module. If i lies
outside the support this instead forces r = 0. Compose the contractions and apply
the associated-sheaf functor, identifying pullbacks of free sheaves with free
sheaves. This gives the stated homotopy equivalence. No neighbourhood is asserted. -/
theorem nonempty_stalk_homotopyEquiv_single_of_residue
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) (y : Y)
    (hy : (∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
          P).homology q)) ∧
      ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r) :
    Nonempty (HomotopyEquiv
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P)
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules (i : ℤ)).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
