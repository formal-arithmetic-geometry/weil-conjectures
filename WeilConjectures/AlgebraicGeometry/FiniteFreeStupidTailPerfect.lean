/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-! # Perfectness of finite-free stupid tails

Source: Stacks Project, Tag 08EG, finite-free tail in the proof of Lemma 36.13.6;
Definition 08C4 (blueprint: lem-sc-finite-free-stupid-tail-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products

end AlgebraicGeometry.Scheme
