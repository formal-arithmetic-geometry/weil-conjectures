/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Zeroth Fitting ideal of a finite module

Source: Stacks Project, More on Algebra, Tags 07Z8 and 07ZA (blueprint: def-trf-fitting-ideal-zero).

This module chooses a finite free surjection and takes its zeroth kernel-minor ideal.  The
recorded presentation-independence theorem makes this choice independent of the surjection.
-/

@[expose] public section

universe u v

namespace LinearMap

/-- The zeroth Fitting ideal of a finitely generated module, obtained from a finite free
surjection.  Independence of the chosen surjection is
`presentationFittingIdeal_independence_baseChange` (blueprint: def-trf-fitting-ideal-zero). -/
noncomputable def fittingIdealZero {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] : Ideal R :=
  let h := Module.Finite.exists_fin' R M
  let hn := Classical.choose_spec h
  let π := Classical.choose hn
  π.presentationFittingIdeal 0

end LinearMap
