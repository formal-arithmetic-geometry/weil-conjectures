/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Sectionwise ordinary projection of the quotient pullback mate

Source: Stacks 03D7 and 0941; primitive coefficient comparisons in
`fix-prop-coherence.proof.md`.
(blueprint: lem-sf-pull-quotient-ordinary-projection-section)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite projection identity on one cochain degree and one section.

Source: Stacks Project, Tags 03D7, 03EL and 0941; current blueprint
`sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`,
ordinary projected-section calculation.

Proof: evaluate the ordinary reduction/limit mate at the chosen degree and
section. The unit identity for the conjugate adjunction identifies its finite
projection with the scalar adjunction unit. The inverse-image and reduction
evaluation normalizations cancel the comparison factors in the strict pullback
tower. The generators equation of the prescribed pull presentation identifies
the resulting finite unit with the quotient augmentation followed by the tower.
The argument is purely sectionwise and applies to zero complexes and empty
sites as well.
-/
theorem pullQuotientOrdinaryProjection_section
    (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : OpenFactorCoherence.Pull l E f)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
    (V : X.ProEtᵒᵖ)
    (x : (((OpenFactorCoherence.pullCx l E f).obj P).X i).val.obj V) :
    (((((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).unit.app
      ((OpenFactorCoherence.pullCx l E f).obj P) ≫
      ((pullbackTensorOrdinaryLimit l E X).mapHomologicalComplex (.up ℤ)).map
        (a.reductionPullComplex l E f P) ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E X ⋙
          pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
            (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P))) ≫
      (pullbackTensorPullbackTower l E f P).hom.app (op n)).f i).val.app V x) =
      (((((IntegralOnSlice.augmentation l E X none).app
        ((OpenFactorCoherence.pullCx l E f).obj P)).app (op n) ≫
        (p.tower.hom.app P).app (op n)).f i).val.app V x) := by
  sorry

end WeilConjectures.GeneratorReduction
