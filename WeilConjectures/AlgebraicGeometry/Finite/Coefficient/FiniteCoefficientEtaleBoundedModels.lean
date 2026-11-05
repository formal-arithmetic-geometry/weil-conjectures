/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleSliceOrigin
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSiteBoundedConstantModels
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink

/-! # Bounded constant models from finite etale-local cohomology

Source: Stacks Project, Tags 09AL and 094G
(blueprint: lem-weil-pbc-finite-coefficient-etale-bounded-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
