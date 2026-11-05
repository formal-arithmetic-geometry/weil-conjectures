/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Pi

/-! # The finite-partition principal w-localization

Source: blueprint, proper base change, definition of the affine w-localization, order 1222
(blueprint: def-weil-pbc-w-localization).

The indices remember both the finite constructible partition and its denominators.
Refinement requires divisibility of denominators, so the component localization maps exist.
This construction is distinct from the upstream `WLocalization`, whose stages use localizations
at larger submonoids. No geometric property or comparison with that construction is asserted.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

variable (A : Type u) [CommRing A]

variable {A}

attribute [instance] index_isFiltered

end PrincipalWLocalization
