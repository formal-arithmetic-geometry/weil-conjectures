/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Images

import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Comparing extended ideal tensor products with categorical images

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX, displayed conductor equality;
Modules Tag 01CD. The general image identification below is the representation step.
(blueprint: lem-sc-ideal-tensor-image-comparison).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

end AlgebraicGeometry.Scheme.Modules
