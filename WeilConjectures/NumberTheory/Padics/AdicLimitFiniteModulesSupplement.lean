/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import WeilConjectures.RingTheory.PoincareDuality.AdicTowerReconstruction
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import WeilConjectures.RingTheory.FiniteModuleComplete

/-!
# Adic systems of finite modules over p-adic coefficient rings

Source: Stacks Project, Tags 09B8, 031D, 031B and 00MA;
blueprint `cor-galois-lisse-representations`, steps 6, 7, 9 and 10
(blueprint: lem-pod-adic-limit-finite-modules).

Indices `n : ℕ` denote the positive exponent `n + 1`. A module over the coefficient
quotient is represented by its underlying module over the valuation ring, annihilated
by the corresponding ideal. Surjectivity and the specified kernel say that the
transition induces the required quotient isomorphism.
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped Pointwise
open Topology

namespace Padic

end Padic
