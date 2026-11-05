/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The affine nonvanishing locus of a section of an invertible module

Source: Stacks Project, Properties, Lemma 01PV (`properties-lemma-affine-cap-s-open`),
algebra argument in the proof (blueprint: lem-sc-affine-cap-section-open-algebra).
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace AlgebraicGeometry

-- Construct the localization comparison and its inverse on a trivializing chart.
-- Transport the algebra calculation to the actual restricted spectrum morphism.

-- The quotient relation excludes primes at which the section vanishes.

-- A projective splitting detects nonvanishing by a coordinate functional.

-- Normalize that functional in the residue field and take the evaluation kernel.

end AlgebraicGeometry
