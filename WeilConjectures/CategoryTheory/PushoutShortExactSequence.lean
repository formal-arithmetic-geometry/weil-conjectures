/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Pushout of a short exact sequence

Source: Stacks Project, Homology, Tags 010I (extensions, item (2)), 05PJ (pushout as
cokernel), 08N4 (monomorphisms in pushouts), and 08N3 (cokernels in pushouts)
(blueprint: lem-weil-pbc-pushout-short-exact-sequence).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] Abelian.hasFiniteBiproducts

end CategoryTheory
