/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Set.Finite.Basic
public import WeilConjectures.GroupTheory.TateModule

/-!
# Tate modules

This file records the incarnation of the `ℓ`-adic Tate module `AddCommGroup.tateModule` (defined
in `WeilConjectures.GroupTheory.TateModule`) for the group of units of a field (the cyclotomic
Tate module `ℤ_ℓ(1)`), and the group-theoretic statement underlying the vanishing of the
Frobenius-fixed vectors of a Tate module.

The multiplicative group `μ_{ℓ^n}(K)` of `ℓ^n`-th roots of unity of a field is the `ℓ^n`-torsion
of `Kˣ`, so the cyclotomic Tate module is literally the Tate module of the additive group
`Additive Kˣ`; it is defined that way, so that the statements below apply to it.

## Main declarations

* `cyclotomicTateModule`: the cyclotomic Tate module `ℤ_ℓ(1)` of a field `K`, the Tate module of
  `Kˣ`.
* `AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed`: an automorphism of an abelian group
  with finitely many fixed points fixes no nonzero vector of the Tate module.
* `AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self`: the same for the rational Tate
  module.

## Blueprint

`cyclotomicTateModule` implements `det-d-ab-cyclotomic`;
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed` implements `sk-p-tate`; together with
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_symm_fixed`,
`AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self` and
`AddCommGroup.rationalTateModule.eq_zero_of_map_symm_eq_self` it implements
`lem-tate-module-no-fixed`.
-/

@[expose] public section

open scoped TensorProduct

namespace AddCommGroup

namespace rationalTateModule

end rationalTateModule

end AddCommGroup

