/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwistMono
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwistImage

/-! # Restricting a disjoint ideal times an invertible module

Source: Stacks Project, Varieties Remark 09NW and the local trivialization argument in
Lemma 09NX (blueprint: lem-sc-closed-immersion-disjoint-ideal-twist).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
