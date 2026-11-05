/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.PositiveTensorFamily
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor sections and affine nonvanishing loci

Source: Stacks Project, Varieties Lemma 09NC, proof, invoking Properties Lemma 01PV
(blueprint: lem-sc-tensor-section-affine-open).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

end AlgebraicGeometry.Scheme.Modules
