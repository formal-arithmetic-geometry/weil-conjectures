/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.AffineTildeTotalTensor
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Affine computations of derived pullback and tensor

Source: Stacks Project, Lemmas 36.3.8(2), 36.3.9(2), Tags 08DW and 08DX,
and Lemma 36.3.6, Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).

The affine formulas are written for every K-flat resolution `P ⟶ M`.
Thus the right sides are the concrete representatives of the module derived tensors,
with no boundedness, flatness of the ring map, or quasi-coherence hypothesis added.

## Main statements

- `derivedPullback_openRestriction_iso`: restriction of derived pullback.
- `derivedTensor_openRestriction_iso`: restriction of derived tensor, natural in both factors.
- `derivedPullback_tilde_iso`: affine pullback on any K-flat resolution.
- `derivedTensor_tilde_iso`: affine tensor on any K-flat resolution of the first factor.
- `derivedPullback_tilde_kFlat_natIso`: natural affine pullback comparison on K-flat models.
- `derivedTensor_tilde_kFlat_natIso`: natural affine tensor comparison on K-flat models.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
