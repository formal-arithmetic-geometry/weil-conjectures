/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

public import Mathlib.Algebra.Homology.Homotopy

/-! # Local homotopy normal form after pullback at a good residue point

Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-residue-local-homotopy)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Local homotopy normal form after pullback at a good residue point.

Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-residue-local-homotopy).

Proof: At the local ring at g(z), split a unit differential coefficient until none
remain. Each cancellation lowers the finite total rank. The remaining residue
differentials are zero, hence the residue hypothesis forces just r generators in
degree i. All other terms have rank zero. The basis changes, their inverses, and
contracting homotopies involve finitely many functions, so they extend to an open
neighbourhood of g(z). Pull back that neighbourhood and the explicit homotopies
along g. Restriction to the inverse image open gives the stated homotopy equivalence.
This uses no reducedness. If r = 0 the minimal complex is zero; if i > d the
hypothesis forces r = 0. There is no point to check on an empty source. -/
theorem exists_restrict_homotopyEquiv_single_of_residue
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) {Y' : Scheme.{u}} (g : Y' ⟶ Y) (z : Y')
    (hz : (∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback (Y.fromSpecResidueField (g.base z))).mapHomologicalComplex _).obj
          P).homology q)) ∧
      ((((Modules.pullback (Y.fromSpecResidueField (g.base z))).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r) :
    ∃ U : Y'.Opens, z ∈ U ∧ Nonempty (HomotopyEquiv
      (((restrictFunctor U.ι).mapHomologicalComplex _).obj
        (((Modules.pullback g).mapHomologicalComplex _).obj P))
      ((CochainComplex.singleFunctor U.toScheme.Modules (i : ℤ)).obj
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
