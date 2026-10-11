/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Ext vanishing over a regular local ring

Source: Stacks Project, Derived Categories of Varieties, Lemma Tag 0FZ3, proof of (1), invoking
Algebra Proposition Tag 00O7 (blueprint: lem-sc-regular-local-ext-vanishing).
-/

universe u v

open CategoryTheory

namespace IsRegularLocalRing

/-- Over a regular local ring, Ext from a finite module to any module vanishes above
its Krull dimension. Source: Stacks Project, Tag 0FZ3, proof of (1), and Tag 00O7
(blueprint: lem-sc-regular-local-ext-vanishing).

Proof: by `lem-weil-pbc-regular-local-finite-gl-dim` (Tag 00O7), every module over `R`
has a projective resolution of length at most `d = dim R`. This dimension is finite:
`R` is Noetherian local and its maximal ideal has a finite set of generators.
Apply `lem-weil-pbc-projective-dimension-ext-characterization` (Tag 065R) with
`X = M` and `n = d`. The resolution gives vanishing of Ext to every `N` in degrees
at least `d + 1`. The hypothesis `q > d` is equivalent to `q ≥ d + 1`, giving the
claim. The finite-module assumption on `M` is retained, although Tag 00O7 works
for every module. Natural degrees cover exactly the integers above the nonnegative
dimension of a regular local ring, as required by `def-pc-ext`. -/
theorem subsingleton_ext_of_ringKrullDim_lt
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M N : ModuleCat.{v} R) [Module.Finite R M]
    (q : ℕ) (hq : ringKrullDim R < (q : WithBot ℕ∞)) :
    letI := HasExt.standard (ModuleCat.{v} R)
    Subsingleton (Abelian.Ext M N q) := by
  sorry

end IsRegularLocalRing
