/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Residue detection of pulled-back single cohomology

Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-pullback-residue-criterion)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Single finite locally free cohomology of a pulled-back bounded nonnegative finite
free complex is detected by the residue cohomology at all image points.

Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: lem-pc-finite-free-pullback-residue-criterion).

Proof: at any image point satisfying the residue condition, split unit entries over
its local ring as in lem-weil-pbc-free-complex-unit-entry-splits. The resulting minimal
complex has rank r in degree i and rank zero elsewhere. Spread the finite sequence
of cancellations to a neighbourhood. Pullback preserves the explicit homotopies and
contractible summands, so its cohomology on the inverse image neighbourhood vanishes
off i and is free of rank r in degree i. These neighbourhoods cover the source;
vanishing and finite local freeness glue.
Conversely, the pulled-back complex has zero cohomology off i and locally free rank-r
cohomology in degree i. Its negative cohomology is zero by nonnegative support.
Truncation identifies it locally with that flat sheaf in degree i. Its derived fibre
is thus the residue field to the r-th power in degree i. The terms of the original
complex are free, so termwise pullback computes both derived fibres. At a source
point z over y this fibre is the scalar extension from κ(y) to κ(z) of the fibre at y.
A field extension is faithfully flat and preserves finite-dimensional cohomology
ranks (lem-pc-finrank-field-base-change); hence the fibre at y has the same vanishing
and rank. This proves the criterion, also for the empty source and rank zero. -/
theorem finiteFree_pullback_single_iff_residue
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    ((∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) ∧
      ((((Modules.pullback g).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r) ↔
      ∀ y ∈ Set.range g.base, ((∀ q : ℕ, q ≠ i → IsZero
          ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
            P).homology q)) ∧
        ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
          P).homology i).IsFiniteLocallyFreeOfRank r) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
