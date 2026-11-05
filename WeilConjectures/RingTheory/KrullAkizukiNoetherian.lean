/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.RingTheory.FiniteLengthGlobalSubmodule

/-!
# Krull–Akizuki Noetherianity for intermediate rings

Source: Stacks Project, Algebra, Lemma 10.119.12 (Tag 00PG)
(blueprint: lem-sc-krull-akizuki-noetherian).
-/

@[expose] public section

universe uR uD uK uL

