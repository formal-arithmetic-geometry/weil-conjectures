/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import WeilConjectures.RingTheory.FactorsThroughLocalization
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.FilteredColimitOfFactorization

/-! # Local-ring identifications with w-local target

Source: blueprint, proper base change, `sk-thm-properbasechange`, lemma
`lem-weil-pbc-local-rings-ind-zariski`
(blueprint: lem-weil-pbc-local-rings-ind-zariski).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

open scoped BigOperators

end Algebra
