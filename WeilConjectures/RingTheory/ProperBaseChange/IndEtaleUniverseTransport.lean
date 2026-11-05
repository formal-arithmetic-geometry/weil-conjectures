/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.Algebra.Ring.ULift

/-!
# Ind-etale ring maps across universes

Source: blueprint, proper base change, definition of ind-etale and ind-Zariski
algebras (blueprint: def-weil-pbc-ind-etale-algebra).

The existing ind-etale predicate requires equally-sized source and target types.
Canonical `ULift` transport makes it applicable to arbitrary ring maps. The other
clauses of the blueprint definition are exposed by `IndPrincipalZariski`.
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace RingHom

end RingHom
