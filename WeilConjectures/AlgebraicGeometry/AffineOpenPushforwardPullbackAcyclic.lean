/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.AffineOpenPushforwardAcyclic
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Acyclicity after pullback of an affine-open direct image

Source: Stacks Project, Tag 02KG, and the affine intersection paragraphs of
`lem-pc-s3-affine-alternating-cech-resolution-core`.
(blueprint: lem-pc-s3-affine-open-pushforward-pullback-acyclic).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
