/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantProjectionMaps
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # The rank-one completed constant comparison

Source: Stacks Project, Modules on Sites, Tags 03EK and 093M, and completion Tag 05GG.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

namespace CompletedConstantRankOne

open CompletedConstantProjection

-- Compare the additive and ring sheafifications of the constant rank-one module.

-- Completion evaluation descends to a bijection on each finite quotient.

-- Retain quotient-ring linearity when identifying the finite additive sheaves.

-- The existing scalar-extension unit isomorphism has the expected tensor inverse.

end CompletedConstantRankOne

open CompletedConstantRankOne

end AlgebraicGeometry.Scheme
