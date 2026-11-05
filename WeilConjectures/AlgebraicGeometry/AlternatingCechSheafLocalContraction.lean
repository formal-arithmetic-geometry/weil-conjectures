/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafInsertionHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Local contraction of the increasing-tuple sheaf augmentation

Source: Stacks Project, Tag 01FM, alternating faces; local contraction paragraph of
lem-pc-s3-affine-alternating-cech-augmented-construction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-contraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

-- Restriction detects invertibility on an open cover, including the empty cover.

-- Exact restriction commutes with homology, for any complex shape.

-- Identify the explicit tensor formula with the canonical pullback by adjunction.

-- Pullback followed by open restriction factors through restriction on the source.

end AlgebraicGeometry
