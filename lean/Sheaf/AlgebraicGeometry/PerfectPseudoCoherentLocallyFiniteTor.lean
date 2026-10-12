/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.LocallyFiniteTorDimension
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover

/-! # Perfect complexes are pseudo-coherent and locally of finite Tor dimension
Source: literature/stacks-project/cohomology.tex, Lemma 08CQ, implication (1) => (2)
(blueprint: lem-pc-perfect-pseudo-coherent-locally-finite-tor).
-/

@[expose] public section

universe uP wP
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A perfect complex is pseudo-coherent and locally has finite Tor dimension.
Source: literature/stacks-project/cohomology.tex, Lemma 08CQ, implication (1) => (2)
(blueprint: lem-pc-perfect-pseudo-coherent-locally-finite-tor).

Proof: refine a strictly perfect local model by affine opens and finite-free principal
opens (`lem-weil-pbc-finite-projective-standard-free-cover`); this gives the
bounded-above finite-free models required for pseudo-coherence.
This uses `def-pc-perfect-complex` and `def-pur-pseudo-coherent-complex`.
The same bounded model is termwise flat and K-flat by the bounded-above-flat K-flat
lemma (`lem-pc-bounded-above-flat-kflat`), and its tensor with any module is bounded
in one common finite interval.
-/
theorem perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension (X : Scheme.{uP})
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    IsPseudoCoherent X E ∧ HasLocallyFiniteTorDimension X E := by
  sorry

end AlgebraicGeometry.Scheme
