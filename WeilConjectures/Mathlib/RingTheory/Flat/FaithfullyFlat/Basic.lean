/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Adjoining a root of a monic polynomial is faithfully flat

For a monic polynomial `f : R[X]` of nonzero degree, `R[X]/(f)` is a free `R`-module with basis
`1, X, …, X^(deg f - 1)`, hence faithfully flat over `R`.

## Main results

- `AdjoinRoot.faithfullyFlat_of_monic`: `R[X]/(f)` is faithfully flat over `R` for `f` monic of
  nonzero degree.
-/

@[expose] public section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- For a monic polynomial `f` of nonzero degree, `R[X]/(f)` is faithfully flat over `R`: it is
free with basis `1, X, …, X^(deg f - 1)`, and nonzero when `R` is. -/
theorem faithfullyFlat_of_monic {f : R[X]} (hf : f.Monic) (hdeg : f.degree ≠ 0) :
    Module.FaithfullyFlat R (AdjoinRoot f) := by
  let pb := powerBasis' hf
  have := Module.Free.of_basis pb.basis
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨fun m hm ↦ (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  have hdim : 0 < pb.dim := by
    rw [degree_eq_natDegree hf.ne_zero] at hdeg
    simpa [pb] using Nat.pos_of_ne_zero (by exact_mod_cast hdeg)
  have : Nontrivial (AdjoinRoot f) :=
    nontrivial_of_ne _ 0 (pb.basis.linearIndependent.ne_zero ⟨0, hdim⟩)
  infer_instance

end AdjoinRoot
