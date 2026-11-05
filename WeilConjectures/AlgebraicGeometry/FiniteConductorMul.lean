/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! The ideal-power form of the finite conductor statement.

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2.
(blueprint: semilocal-dim-one-conductor-power-mul)
-/
@[expose] public section
universe u v

