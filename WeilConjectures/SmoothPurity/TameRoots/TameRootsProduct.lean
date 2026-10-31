/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.CategoryTheory.CofilteredSystem
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms

/-!
# Compatible tame roots and the product of adic integers

Source: Stacks Project, fields.tex Tag 09HW, algebra.tex Tags 00DT and 00M9;
blueprint main-20261015, proof of `lem-exc-dvr-galois`, second paragraph
(blueprint: lem-exc-tame-roots-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace TameRoots

private abbrev Away (p : ℕ) := {r : Nat.Primes // (r : ℕ) ≠ p}

end TameRoots
