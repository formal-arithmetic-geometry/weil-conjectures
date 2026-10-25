/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# Geometric generic fibres of henselian lifts over the trait

Let `k'` be a separably closed field, `A = k'⟦t⟧` and `C̄` a w-contractible ind-étale
`A ⧸ (t)`-algebra. Its henselian lift `H = H_A(C̄)` is a filtered colimit of finite products
of copies of `A` (an étale `A`-algebra over the strictly henselian `A` is a product of copies of
`A` and of an algebra on which `t` is invertible, and the latter maps to zero in `C̄`). Hence
the geometric generic fibre `H ⊗_A Ω` is a filtered colimit of finite products of copies of the
algebraically closed field `Ω`, with the same extremally disconnected space of connected
components as `C̄`: it is w-contractible, and the base change of `W = Spec H` to the geometric
generic point `Spec Ω ⟶ S` is weakly contractible
(`AlgebraicGeometry.ProEtale.isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {k' : Type u} [Field k'] [IsSepClosed k']

/-- The henselian lift `W = Spec H_{k'⟦t⟧}(C̄)` of a w-contractible ind-étale
`k'⟦t⟧ ⧸ (t)`-algebra `C̄` has a weakly contractible geometric generic fibre
`W ×_S Spec Ω`. -/
theorem isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec (C : Type u) [CommRing C]
    [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C] [Algebra (PowerSeries k') C]
    [IsScalarTower (PowerSeries k') (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C] (hC : IsWContractibleRing C) :
    (ProEt.topology (Spec (.of (traitGenericField k')))).IsWeaklyContractible.{u + 1}
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (traitGenericPoint k')).obj
        (closedLiftSpec (.of (PowerSeries k')) C)) :=
  sorry

end AlgebraicGeometry.ProEtale
