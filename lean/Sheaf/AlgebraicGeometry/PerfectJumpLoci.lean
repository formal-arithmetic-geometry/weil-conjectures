/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Semicontinuity.Basic

/-! # Jump loci of pseudo-coherent complexes

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.31.1, Tag 0BDI
(blueprint: lem-sc-perfect-jump-loci).
-/

@[expose] public section

universe uX wX

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Fibre cohomology dimensions of a pseudo-coherent complex commute with arbitrary
base change, are upper semicontinuous, and have locally constructible level sets.
Source: Stacks Project, Tag 0BDI (blueprint: lem-sc-perfect-jump-loci).

Proof:
1. Locally on an affine neighbourhood represent `E` by a bounded-above finite-free
   complex using def-pur-pseudo-coherent-complex. Its stupid truncation in degrees
   at least `i-1` is bounded finite free and preserves degree-`i` fibre cohomology.
   Termwise tensor computes the derived fibres by lem-pc-flat-complex-derived-pullback.
2. Apply lem-sc-finite-free-complex-homology-upper-semicontinuous on each neighbourhood;
   upper semicontinuity is local and hence holds on `X`.
3. Pull the same model back along `g`. At `y`, it is the scalar extension from
   `κ(g y)` to `κ(y)` of the original fibre. Field extensions are flat and preserve
   cohomology dimensions, giving the base-change formula. On each affine neighbourhood
   the strict sublevel sets are quasi-compact opens by the finite-free homology lemma.
   Such opens are retrocompact (Tag 054D), and each level set is the difference of
   two such opens, hence constructible (Tag 005G). This proves local constructibility.
-/
theorem pseudoCoherent_jump_loci (X : Scheme.{uX})
    [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{wX} (SheafOfModules.{uX}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (i : ℤ) :
    (∀ (Y : Scheme.{uX})
      [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))]
      [∀ y : Y, HasDerivedCategory.{wX} (SheafOfModules.{uX}
        (moduleRings (Spec (Y.residueField y)).toRingedSpace))]
      (g : Y ⟶ X) (y : Y),
        derivedFiberBetti Y ((derivedPullback g).obj E) i y = derivedFiberBetti X E i (g y)) ∧
      UpperSemicontinuous (derivedFiberBetti X E i) ∧
      ∀ r : ℕ, Topology.IsLocallyConstructible {x : X | derivedFiberBetti X E i x = r} := by
  sorry

end AlgebraicGeometry.Scheme
