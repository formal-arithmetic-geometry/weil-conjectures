/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Finitely generated modules over a discrete valuation ring

A finitely generated module over a discrete valuation ring is the product of a finite free
module and a module killed by a power of the uniformizer.
-/

@[expose] public section

universe u v

open DirectSum

namespace Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

end Module
