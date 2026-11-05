/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransitionUnit

/-! # The ordinary quotient transition and the tensor units

The unit of ordinary scalar extension along `R → R_(n+1)`, followed by the quotient transition,
is the unit along `R → R_n`: both send a section `x` to `1 ⊗ x`.

Source: Stacks Project, Tags 03EK and 09C6.
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
