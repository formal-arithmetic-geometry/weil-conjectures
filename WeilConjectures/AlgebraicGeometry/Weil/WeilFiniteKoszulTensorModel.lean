/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal

/-! # An algebraic intermediate for the finite Koszul comparison

The ordered tensor is formed over the original coefficient ring, before sheafification
or coefficient extension. Its factors are the existing one-generator exterior complexes.
Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: def-weil-pbc-finite-negative-koszul-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

end AlgebraicGeometry.Scheme
