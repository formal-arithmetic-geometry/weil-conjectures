/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralTower.PurStrictIntegralExchangeData

/-! # PurIntegralStrictReduction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The specified strict proper/open maps commute with quotient reduction and all
canonical finite corners.

Source: constituent compatibility, strict integral normalization steps 2--3,
7--8 and 13--14 (blueprint: lem-pur-integral-strict-reduction).

Proof: on a flat-term K-flat representative of the whole diagram, both pullback
unit and compositor comparisons send each pure tensor to the same tensor with
its relabeled quotient scalar, proving the first two equations. The proper
projection is the counit-tensor adjunct. Apply the strict exchange/projection
rectangle to identify towerV with the reduced ambient mate; naturality of
completedReductionEvaluation gives its finite square with the prescribed corners
0 and 2. Corners 1 and 3 are defined by conjugating with H and H prime, so their
squares follow by canceling those isomorphisms. The four-arrow rectangle and
v prime = H inverse, v, H prime give the fourth equation. For the open scalar
square use the generator-normalized strict open comparison, whose inverse is the
pulled open unit. Scalar restriction and open reduction preserve that unit,
proving the strict equality before evaluation. completedRingStrictFiniteExchange
gives its finite square. Whisker the strict proper reduction rectangle with open
extension, then use the strict open square and naturality of towerProjection.
Cancel adjacent proper and open reduction isomorphisms to obtain the exchange
reduction square with exactly exchangeReductionSource and exchangeReductionTarget.
For composition do the same with its proper/open mate and open compositor; the
proper projection comparisons are mates of the tensor comparisons and therefore
respect pasting. This gives the square with compositionReductionSource and
supportReduction. Apply the evaluation functor and naturality of
completedReductionEvaluation to each of these last two strict squares; its fixed
finiteCorner is precisely the resulting corner. Every construction retains all
quotient transitions. No faithfulness of evaluation or choice of finite corners
is used. Zero complexes, empty schemes and the zero level index n = 0 satisfy the
same identities (the latter denotes the positive quotient exponent 1). -/
theorem purIntegralStrictReduction (P : WeilConjectures.PurityFiniteSetting.{t}) :
    PurIntegralStrictReduction (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) := by sorry

end AlgebraicGeometry.Scheme
