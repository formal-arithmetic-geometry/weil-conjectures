/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections
public import WeilConjectures.TraceFormula.Specialization.Trait
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftConnectedComponents
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftStrictlyHenselian
public import WeilConjectures.RingTheory.ProEtale.SpanIdempotents

/-!

# Geometric generic fibres of henselian lifts over the trait

Let `k'` be a separably closed field, `A = k'⟦t⟧` and `C̄` a w-contractible ind-étale
`A ⧸ (t)`-algebra. Its henselian lift `H = H_A(C̄)` is a filtered colimit of finite products
of copies of `A` (an étale `A`-algebra over the strictly henselian `A` is a product of copies of
`A` and of an algebra on which `t` is invertible, and the latter maps to zero in `C̄`). Hence
the geometric generic fibre `H ⊗_A Ω` is a filtered colimit of finite products of copies of the
algebraically closed field `Ω`, with the same extremally disconnected space of connected
components as `C̄`: it is w-contractible
(`AlgebraicGeometry.ProEtale.isWContractibleRing_closedLift_tensorProduct_traitGenericField`), and
the base change of `W = Spec H` to the geometric
generic point `Spec Ω ⟶ S` is weakly contractible
(`AlgebraicGeometry.ProEtale.isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec`).

-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {k' : Type u} [Field k'] [IsSepClosed k']

end AlgebraicGeometry.ProEtale
