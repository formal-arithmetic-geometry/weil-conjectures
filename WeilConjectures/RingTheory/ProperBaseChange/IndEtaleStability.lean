/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.CategoryTheory.Limits.Comma

import Mathlib.RingTheory.Localization.Pi

/-! # Stability of ind-etale and principal ind-Zariski maps

Source: blueprint, proper base change, lemma "Stability and diagonal of an ind-etale algebra"
(blueprint: lem-weil-pbc-ind-etale-stability).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

-- Finite principal-localization blocks and their explicit base changes.

-- Relate the algebra presentation to the categorical ind-property.

-- Localization and finite products preserve the blocks, including empty products.

-- Descend the finite list of denominators to one filtered stage.

-- Push out to a fixed source, then construct the colimit universal property.

-- The remaining clauses use existing ind-etale and weakly etale APIs.

namespace RingHom

end RingHom
