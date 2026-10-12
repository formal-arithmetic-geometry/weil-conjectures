/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Spreading a finite free homotopy normal form from a stalk

Source: blueprint lem-pc-perfect-locus, proof step 4 (finite matrix identities).
(blueprint: lem-pc-finite-free-stalk-homotopy-spread)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A homotopy equivalence with a single free complex over a local ring spreads.

Source: blueprint lem-pc-perfect-locus, proof step 4, finite matrix extension argument.
(blueprint: lem-pc-finite-free-stalk-homotopy-spread).

Proof: Work on an affine neighbourhood of y and choose finite bases of P's terms.
Both complexes have finite support. Under the affine quasicoherent module-sheaf
correspondence, the given maps and the two homotopies are finite lists of matrices
with entries in the local ring at y. Represent their finitely many entries by
sections on neighbourhoods of y, and intersect those neighbourhoods. Chain-map
commutativity and the two homotopy equations are finitely many entrywise equations
of sections. Each holds in the stalk, so after shrinking around y each holds as an
equation of sections; intersect this second finite list of neighbourhoods. All
components outside the bounded support are the unique maps from or to zero objects,
so there are no further equations to impose. The represented matrices now define
chain maps and homotopies on the resulting open V, proving that the composites are
homotopic to the identities. No residue cohomology or base change is used here. -/
theorem exists_restrict_homotopyEquiv_single_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i : ℤ) (r : ℕ) (y : Y)
    (hy : Nonempty (HomotopyEquiv
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P)
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))) :
    ∃ V : Y.Opens, y ∈ V ∧ Nonempty (HomotopyEquiv
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
