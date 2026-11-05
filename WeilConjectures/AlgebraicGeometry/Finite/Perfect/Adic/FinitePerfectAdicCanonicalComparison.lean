/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientDiagram
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicFlatTensorComparison
import Mathlib.RingTheory.Finiteness.Projective

/-! # The canonical quotient diagram as an explicit coefficient complex

Source: Stacks Project, Tag 09C6, the finite-projective quotient comparison;
Modules on Sites, Tags 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
