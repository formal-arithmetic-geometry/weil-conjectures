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
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwist

/-!
# Conductor ideal: zero intersection and restriction to a component

Source: literature/stacks-project/varieties.tex, Varieties Remark 09NW, as used in the proof
of Lemma 09NX (blueprint: lem-sc-conductor-ideal-zero-intersection).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry

open Scheme

end AlgebraicGeometry
