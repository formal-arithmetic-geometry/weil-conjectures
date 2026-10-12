/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeResidueIso
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.PerfectSummand

/-! # The degree-zero residue-field criterion for a perfect complex

Source: Stacks Project, Tag 0E62, proof of Lemma 36.32.5
(blueprint: lem-sc-perfect-degree-zero-fibre-criterion).

Residue-field tensor is derived pullback along `S.fromSpecResidueField s`. Its cohomology
is a sheaf on `Spec κ(s)`, equivalently a `κ(s)`-module. Restriction to an open subscheme
is derived pullback along its inclusion. The structure sheaf is `SheafOfModules.unit`
placed in degree zero. The positive Tor-amplitude condition tests every module sheaf.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A perfect object whose negative derived fibres vanish and whose degree-zero fibre map
from the structure sheaf is an isomorphism has an isomorphism on degree-zero cohomology,
and locally splits as the structure sheaf plus a perfect object of positive Tor-amplitude.
Source: Stacks Project, Tag 0E62, proof of Lemma 36.32.5
(blueprint: lem-sc-perfect-degree-zero-fibre-criterion).

Proof:
1. At each point use lem-sc-perfect-finite-free-residue-model to represent K on an affine
   neighbourhood by a bounded finite free complex with ranks equal to fibre cohomology
   dimensions. Its negative terms vanish. Termwise tensor computes derived tensor, giving
   Tor-amplitude [0, infinity) locally and hence globally, and no negative cohomology.
2. The map u factors through H^0(K)[0]. Its fibre isomorphism makes the comparison from
   H^0(K) tensor κ(s) to H^0(K tensor^L κ(s)) surjective. Apply
   lem-sc-perfect-cut-complex-degree-zero to split K locally as H^0(K)[0] plus a perfect
   complex of Tor-amplitude [1, infinity).
3. The degree-zero summand is perfect by lem-pc-perfect-summand and flat by its nonnegative
   Tor-amplitude. On an affine, lem-pc-perfect-affine-bounded-projective gives a bounded
   finite projective model. Split its exact positive tail from the top: the degree-zero
   cycles are finite projective, so their cokernel is finitely presented. Apply
   lem-weil-pbc-finitely-presented-flat-module-projective; H^0(K) is finite locally free.
4. The local splitting and flatness identify the degree-zero fibre with H^0(K) tensor κ(s).
   Thus H^0(u) is an isomorphism on every residue fibre. Apply
   lem-sc-finite-locally-free-residue-isomorphism to the finite locally free source and
   target. Substitute this isomorphism into the local splitting to obtain O plus P.
-/
theorem perfect_degreeZero_fibre_criterion (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ (U : S.Opens) (V : U.toScheme.Opens),
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [∀ s : S, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : schemeDerivedQCohProperty S K)
    (hperfect : S.IsPerfect K)
    (u : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings S.toRingedSpace)) ⟶ K)
    (hzero : ∀ s : S, IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map u)))
    (hnegative : ∀ (s : S) (i : ℤ), i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj K))) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map u) ∧
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ P : schemeDerivedCategory U.toScheme,
      U.toScheme.IsPerfect P ∧
      (∀ (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
        i < 1 → schemeDerivedTensorCohomologyVanishes U.toScheme P G i) ∧
      Nonempty ((derivedPullback U.ι).obj K ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace)) ⊞ P) := by
  sorry

end AlgebraicGeometry
