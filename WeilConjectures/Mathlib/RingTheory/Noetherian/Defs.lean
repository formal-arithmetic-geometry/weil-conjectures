/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Bounded torsion in Noetherian modules

In a Noetherian module the `a`-power torsion is killed by a fixed power of `a`
(`IsNoetherian.exists_pow_smul_eq_zero_of_pow_smul_eq_zero`): the increasing chain of the
kernels of `aᵏ` stabilizes.
-/

@[expose] public section

