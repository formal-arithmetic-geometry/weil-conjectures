/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

public import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy normal form of a field fibre of single locally free cohomology

Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-single-field-fibre)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Homotopy normal form of a field fibre of single locally free cohomology.

Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-single-field-fibre).

Proof: The support bound makes negative cohomology zero. With the assumed
nonnegative vanishing, truncation identifies P in the derived category with its
locally free degree-i cohomology in degree i. A locally free sheaf is flat; its
derived fibre is its ordinary fibre, a vector space of dimension r. The bounded
free terms of P compute the derived fibre by termwise pullback. On Spec R,
module sheaves are equivalent to R-vector spaces. A complex of vector spaces
splits into its cohomology and contractible two-term summands by choosing
complements of boundaries in cycles and of cycles in each term. Since the only
cohomology is R^r in degree i, these splittings give a homotopy equivalence to
the displayed single complex. The construction also works for the zero complex
and rank zero, and for i beyond the support (where the hypotheses force r = 0). -/
theorem nonempty_homotopyEquiv_single_field_fibre
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ)
    (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r)
    {R : CommRingCat.{u}} (hR : IsField R) (f : Spec R ⟶ Y) :
    Nonempty (HomotopyEquiv (((Modules.pullback f).mapHomologicalComplex _).obj P)
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r))))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
