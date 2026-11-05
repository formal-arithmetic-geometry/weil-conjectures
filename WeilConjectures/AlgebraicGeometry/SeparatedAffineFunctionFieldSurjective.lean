/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
import WeilConjectures.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.RingTheory.LocalDomainDimOnePrincipalLocalization

/-!
# Separated affine and local charts surject onto the function field

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NB,
proof, separatedness paragraph (blueprint: lem-sc-separated-affine-function-field-surjective)
-/

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

end AlgebraicGeometry
