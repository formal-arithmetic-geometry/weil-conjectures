/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
Definitions moved unchanged by the maintainer L (2026-10-18) out of FiniteRingCompactSupportProjection.lean
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.GroupTheory.Torsion
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.Paper.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj

/-!
# Compact-support projection with arbitrary finite primary coefficients

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Project, Tag 0F0G
(blueprint: def-sp-finite-ring-compact-support-projection-map).

The canonical coefficient realization changes only the presentation of module sheaves.
The projection arrow below is the published counit-defined compactification projection
transported by that realization, on the ordinary unbounded intrinsic derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The specified compact-support projection arrow in intrinsic constant-ring modules.
The fixed-scalar arrow is the counit-defined proper projection, followed by the inverse
open projection and the pullback-composition identification. Apply the canonical derived
realization after evaluating it on the inverse realizations of `M,K`. In particular this
is a natural transformation, with no chosen projection-formula isomorphism or Tor assumption.
Naturality in both arguments is inherited from the published natural transformation.
Source: blueprint Proof (3), tensor-map paragraph; Stacks Tag 0F0G
(blueprint: def-sp-finite-ring-compact-support-projection-map). -/
noncomputable def finiteRingCompactSupportProjection
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (Functor.postcompose₂.obj
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategory).map
      (((((Functor.whiskeringLeft₂ _).obj
        (sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory).obj
          (sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory)).map
            (ProEtale.projectionMapOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c))

end AlgebraicGeometry.Scheme
