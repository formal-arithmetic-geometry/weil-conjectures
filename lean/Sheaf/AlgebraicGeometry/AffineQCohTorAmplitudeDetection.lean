/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffineModuleComplexRepresentative
import Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison
import all Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import Sheaf.Algebra.Homology.TorAmplitudeFlatModel
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison

/-! # Quasi-coherent tests on an affine scheme

Source: Stacks Project, Tag 08EA, affine paragraph, using Tags 06Z0 and 08E9.
(blueprint: lem-pc-affine-qcoh-tor-amplitude-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- On an affine scheme, quasi-coherent test sheaves detect Tor amplitude.
Source: Stacks Project, Tag 08EA, affine paragraph, and Tags 06Z0, 08E9.
(blueprint: lem-pc-affine-qcoh-tor-amplitude-detection).

Proof: Write X as Spec A using its canonical affine spectrum chart. The affine
quasi-coherent derived equivalence represents E by termwise tilde of a module complex M.
Test against tilde N, for every A-module N. The affine tensor comparison and exactness
of tilde identify the tested cohomology with tilde of H^i(M tensor-derived N).
Faithfulness of tilde detects its vanishing, hence M has Tor amplitude [a,b].
The module flat-model criterion gives a flat complex P supported in [a,b] representing M.
Its tilde complex, transported along the canonical chart, is K-flat and represents E.
Tensoring it with any sheaf G in degree zero has zero terms outside [a,b], hence zero
cohomology there. This is a K-flat witness for the conclusion. The argument includes
zero rings, empty affine schemes, unbounded E, and a=b; no arbitrary model is selected
from an unproved mere existence theorem, as only the resulting vanishing is asserted. -/
theorem affineQCoh_torAmplitude_detection (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes X E F i) :
    ∀ G : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by
  sorry

end AlgebraicGeometry
