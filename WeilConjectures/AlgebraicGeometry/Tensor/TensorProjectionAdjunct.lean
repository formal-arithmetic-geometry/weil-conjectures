/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensorSymmetryInvolutive

/-!
# Adjoint of a tensor-projected morphism

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-lem-geo-p1-cohomology/thm-amb-p1-decomposition.proof.md`
(blueprint: lem-amb-tensor-projection-adjunct).

The proof expands the projection-map mate, uses compatibility of the canonical
inverse-image tensor comparison with the signed symmetry, cancels the two opposite
symmetries, and applies naturality and bifunctoriality of the derived tensor product.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
