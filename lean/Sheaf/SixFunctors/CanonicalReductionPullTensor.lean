/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J5
-/
module

public import Sheaf.SixFunctors.GeneratorReductionData

/-! # The ordinary restriction/tensor coefficient square

Source: blueprint fix-prop-coherence, open-adjunction expansion, restriction/tensor step.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction

/-- Ordinary reduction respects the canonical tensor comparison for open restriction.
Source: blueprint latest, sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md, maps-used sentence, restriction/tensor expansion;
Stacks 07A4 and 07A7.
(blueprint: lem-sf-canonical-reduction-pull-tensor).

Proof: choose flat-term K-flat representatives of H and N. Use the representative
normalization of RingedModels.tensor, the ordinary limit projection normalization
of RealizationModel, and its reductionPull model equation. Both composites at
quotient n send a homogeneous tensor x tensor y to
(1 tensor j*x) tensor (1 tensor j*y). The sectionwise equality respects every
coefficient transition, since pullback preserves the quotient projections and
scalar unit. It also respects the signed total differential: on the (a,b)
summand both maps have differential dx tensor y + (-1)^a x tensor dy.
Thus the two maps of strict quotient complexes agree, before derived evaluation.
The canonical ringed and system tensor comparisons localize precisely these
maps. Tensor descent on flat-term K-flat representatives and naturality along
resolving quasi-isomorphisms give the displayed equality on all ordinary
objects. No inverse completion map, open extension or projection formula is
used. The zero complex, identity open and empty open satisfy the same formulas. -/
theorem canonicalReductionPullTensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (H N : DerivedCategory (scalarReductionSource l E X)) :
    let μU := Functor.whiskerRight (eqToIso (o.ringed.tensorClosed U)).hom
      (IntegralSystemRealization.calculus l E U).reduction ≫
        (IntegralSystemRealization.calculus l E U).reductionTensor.hom
    let μX := Functor.whiskerRight (eqToIso (o.ringed.tensorClosed X)).hom
      (IntegralSystemRealization.calculus l E X).reduction ≫
        (IntegralSystemRealization.calculus l E X).reductionTensor.hom
    (IntegralSystemRealization.calculus l E U).reduction.map
        ((IntegralSystemRealization.ringedTensorPull l E o.ringed j).hom.app (H, N)) ≫
        μU.app ((IntegralSystemRealization.ringedPull l E j).obj H,
          (IntegralSystemRealization.ringedPull l E j).obj N) ≫
        (IntegralSystemRealization.calculus l E U).systemClosed.tensor.map
          (Prod.mkHom ((o.realization.reductionPull j).hom.app H)
            ((o.realization.reductionPull j).hom.app N)) =
      (o.realization.reductionPull j).hom.app
          ((o.ringed.tensor X).ordinary.tensor.obj (H, N)) ≫
        (IntegralSystemRealization.pull l E j).map (μX.app (H, N)) ≫
        (pullbackTensorSystemComparison l E j).hom.app
          ((IntegralSystemRealization.calculus l E X).reduction.obj H,
            (IntegralSystemRealization.calculus l E X).reduction.obj N) := by
  sorry

end WeilConjectures.GeneratorReduction
