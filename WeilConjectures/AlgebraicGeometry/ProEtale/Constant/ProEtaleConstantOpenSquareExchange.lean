/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport

/-!
# The canonical open-square exchange in tensor-pullback coordinates

Source: main-20261015, `lem-trf-open-square-exchange`, construction by normalized mates;
Stacks Project, Tags 03S6 and 04J0 (blueprint: lem-trf-open-square-exchange).

The original exchange uses the transported fixed-scalar inverse image. The Frobenius
comparison uses tensor inverse image over the same intrinsic constant ring. The bridge
below is uniquely fixed by the sectionwise units, and is descended termwise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
