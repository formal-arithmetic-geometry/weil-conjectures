/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantPresentationTransport

/-!
# The normalized Koszul-to-quotient comparison over completed coefficients

Source: blueprint, proper base change, Koszul and quotient reconstruction, order 1248;
Stacks Tags 099L, 099M and 0A0E
(blueprint: lem-weil-pbc-completed-koszul-quotient-comparison).

This is the reconstruction comparison in the actual completed coefficient presentation,
with coefficient universe one above the scheme universe. The quotient unit is the
constant-tower adjunction unit followed by the specified strict quotient augmentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
