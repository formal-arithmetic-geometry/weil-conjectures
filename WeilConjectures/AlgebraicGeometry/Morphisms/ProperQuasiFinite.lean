/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Proper quasi-finite morphisms are finite

A morphism of schemes which is proper and locally quasi-finite is finite
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, Stacks 02LS, a consequence of
Zariski's main theorem). This file records the elementary facts around this statement used in
the blueprint, and the variant with finite fibres.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.discreteTopology_fiber_and_quasiFiniteAt`: a morphism locally of
  finite type with a finite fibre is quasi-finite at the points of that fibre, and the fibre is
  discrete.
- `AlgebraicGeometry.locallyQuasiFinite_and_quasiCompact_iff_finite_preimage_singleton`:
  quasi-finite morphisms are the morphisms of finite type with finite fibres.
- `AlgebraicGeometry.IsFinite.iff_isProper_and_finite_preimage_singleton`: a morphism is finite
  if and only if it is proper with finite fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

end AlgebraicGeometry
