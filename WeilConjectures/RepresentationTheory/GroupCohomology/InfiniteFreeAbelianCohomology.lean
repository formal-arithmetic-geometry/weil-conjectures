/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RepresentationTheory.Rep.Iso
import WeilConjectures.RepresentationTheory.GroupCohomology.CupNonvanishing

/-!
# Nonvanishing for an infinite-rank free abelian group

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/`
`sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md` (order 3448, lines 46-50),
the counterexample display and the sentence that `ℤ^n` is a retract of `H`.
(blueprint: lem-sf-infinite-free-abelian-cohomology)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace groupCohomology

/-- Ordinary abstract group cohomology of an infinite-rank free abelian group with trivial
nonzero commutative-ring coefficients is nonzero in every positive degree, expressed as Ext
in the category of left group-ring modules. The coefficient `ULift` only places `R` in the
same universe as the group ring; its action is the canonical trivial action, converted by
`Rep.toModuleMonoidAlgebra`.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/`
`sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md` (order 3448, lines 46-50),
the counterexample display and the retract sentence.
(blueprint: lem-sf-infinite-free-abelian-cohomology)

Proof:
1. For degree `n + 1`, choose `n + 1` distinct indices of `I`. Their coordinate generators
   give a retract from `H = Multiplicative (I →₀ ℤ)` onto `ℤ^(n + 1)`. Equivalently, their
   coordinate homomorphisms and generators form a dual family. The cup-product cocycle has
   alternating pairing `1` with the corresponding fundamental cycle, whereas every
   coboundary pairs to zero. Since `R` is nonzero, this gives a nonzero cohomology class,
   as in `groupCohomology.not_isZero_groupCohomology_finsupp`.
2. The bar resolution identifies this cohomology with Ext of the trivial representation.
   The exact equivalence `Rep.equivalenceModuleMonoidAlgebra` transports its class to Ext
   in left `R[H]`-modules and preserves nonzeroness. `ULift.moduleEquiv` identifies the
   lifted coefficient with `R`, so this is precisely the displayed group-ring Ext.
-/
theorem exists_groupRing_ext_ne_zero_finsupp (R : Type u) [CommRing R] [Nontrivial R]
    (I : Type v) [Infinite I] (n : ℕ) :
    ∃ x : Abelian.Ext.{max u v}
      (Rep.toModuleMonoidAlgebra.obj
        (Rep.trivial R (Multiplicative (I →₀ ℤ)) (ULift.{v} R)))
      (Rep.toModuleMonoidAlgebra.obj
        (Rep.trivial R (Multiplicative (I →₀ ℤ)) (ULift.{v} R))) (n + 1), x ≠ 0 := by
  sorry

end groupCohomology
