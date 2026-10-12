/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFiniteTorDimension
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.AlgebraicGeometry.SheafZeroStalks

/-! # Locality of a fixed Tor amplitude interval

Source: Stacks Project, Cohomology of Sheaves, Lemma 09U9
(cohomology-lemma-tor-amplitude-stalk).
(blueprint: lem-pc-tor-amplitude-open-local).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Tor amplitude in a fixed interval can be checked on open neighbourhoods.
Source: Stacks Project, Cohomology of Sheaves, Lemma 09U9
(cohomology-lemma-tor-amplitude-stalk), its proof using exact stalks and tensor.
(blueprint: lem-pc-tor-amplitude-open-local).

Proof: Fix a global module sheaf G and a degree i outside [a,b]. Choose a K-flat
representative P of E. Its total tensor with G[0] computes the global derived tensor.
For each x choose U from the hypothesis. Exact open restriction preserves K-flatness
and total tensor, so the restriction of this tensor computes E|_U tensor^L G|_U.
The local hypothesis, applied to G|_U and i, says the i-th cohomology of this derived
tensor is zero. Independence of K-flat models identifies this with the restriction of
the i-th cohomology of P tensor G[0]. Its stalk at x is therefore zero. As x was
arbitrary and stalks detect zero sheaves, the global cohomology sheaf is zero.
The chosen P and its localization isomorphism witness the required existential
vanishing predicate. For the empty scheme the stalk argument is vacuous and still
valid, since its only module sheaf is zero. No quasi-coherence or compactness is needed.
-/
theorem torAmplitude_of_open_neighbourhoods (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (a b : ℤ) (hab : a ≤ b)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
        i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes U.toScheme
          ((derivedPullback U.ι).obj E) G i) :
    ∀ (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
      i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by sorry

end AlgebraicGeometry
