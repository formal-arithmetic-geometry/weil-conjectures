/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorReductionAugmentation
public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackReductionAugmentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.CanonicalReductionTensorPull
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperationModels
import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullbackModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedModelExistence
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorModelTransport
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorReductionIdentification
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackAugmentationIdentification

/-! # Tensor and geometric inverse image before the coherent limit

Source: Stacks 03D2 and 07A4. The equation is in the derived category of the
sequence site itself, with no passage to individual derived evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The unit-normalized reduction and inverse-image comparisons form a monoidal
square in the coherent system category, before applying the derived limit.
It holds for arbitrary derived inputs and contains neither completion maps nor
an inverse to a reduction/limit counit.

Source: Stacks 03D2 and 07A4, the ordinary tensor/inverse-image generator calculation;
fix-prop-projection-formula.proof.md, integral reconstruction.
(blueprint: lem-sf-reduction-tensor-pullback).

Proof: take simultaneous flat-term K-flat representatives for M and N. Ordinary
inverse image and coherent reduction preserve these models. Use the signed total
tensor normalizations of proEtaleCanonicalTensorComparison and
pullbackTensorSystemComparison. The reduction and inverse-image comparisons are
unit-preserving by their defining adjunct normalizations; on representatives they
are the unique comparisons of the corresponding composite left adjoints. For a
homogeneous tensor x tensor y, both composites first extend scalars by the quotient
unit and then send the result to the tensor of the two inverse-image unit sections.
The scalar units are multiplicative and natural, so these sections coincide.
Sheafification and total-summand generator extensionality give equality of chain
maps on the actual sequence site. The ordinary quotient transitions agree with
these maps, including ramified transitions. Localize that equality once in the
system category and descend along the product flat K-flat localization. This is
an equality before the derived limit, and does not infer equality from separate
finite derived evaluations. Zero inputs and the empty scheme satisfy the same
generator and totalization formulas. -/
theorem reductionTensorPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : DerivedCategory (integralTowerModules l E Y)) :
    (pullbackReductionComparison l E f).hom.app
        ((tensorModel l E Y).tensor.obj (M, N)) ≫
      (pullbackTensorSequenceDerived l E f).map
        ((tensorReductionComparison l E Y).hom.app (M, N)) ≫
      (pullbackTensorSystemComparison l E f).hom.app
        ((pullbackTensorCalculus l E Y).reduction.obj M,
          (pullbackTensorCalculus l E Y).reduction.obj N) =
    (pullbackTensorCalculus l E X).reduction.map
        ((proEtaleCanonicalTensorComparison f
          ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)
          (tensorModel l E Y) (tensorModel l E X)).hom.app (M, N)) ≫
      (tensorReductionComparison l E X).hom.app
        ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj M,
          (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj N) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackReductionComparison l E f).hom.app M)
          ((pullbackReductionComparison l E f).hom.app N)) := by
  -- Compare the specified models with one normalized realization of the general square.
  obtain ⟨o, _, _⟩ := IntegralSystemRealization.integralSystemOperationModels l E
  obtain ⟨m⟩ := IntegralSystemRealization.integralReductionPullbackModel l E o
  obtain ⟨d, _⟩ := IntegralSystemRealization.integralRingedModelExistence l E
  obtain ⟨eY, heY⟩ := tensorModelIso Y ((PurCompactSupport.completed l E).ring Y)
    (tensorModel l E Y) (d.tensor Y).ordinary
  obtain ⟨eX, heX⟩ := tensorModelIso X ((PurCompactSupport.completed l E).ring X)
    (tensorModel l E X) (d.tensor X).ordinary
  -- The two reduction comparisons are determined by their completion adjuncts.
  have ha : pullbackReductionComparison l E f = m.reductionPull f := by
    apply (pullbackReductionAugmentation_existsUnique l E f).unique
    · exact (pullbackReductionAugmentation_existsUnique l E f).exists.choose_spec
    · intro K
      rw [pullComparison_eq_unit l E f (d.pull f)]
      exact ((GeneratorReduction.primitiveQuotientAugmentations l E d o m).2 f K).2
  let F := PurCompactSupport.pull (PurCompactSupport.completed l E) f
  let SX := pullbackTensorCalculus l E X
  let SY := pullbackTensorCalculus l E Y
  let P := pullbackTensorSequenceDerived l E f
  let μX := Functor.whiskerRight (eqToIso (d.tensorClosed X)).hom SX.reduction ≫
    SX.reductionTensor.hom
  let μY := Functor.whiskerRight (eqToIso (d.tensorClosed Y)).hom SY.reduction ≫
    SY.reductionTensor.hom
  have hbY : (tensorReductionComparison l E Y).hom.app (M, N) =
      SY.reduction.map (eY.hom.app (M, N)) ≫ μY.app (M, N) := by
    exact congrArg (fun z ↦ z.app (M, N))
      (tensorReduction_eq_normalized l E d o m Y eY heY)
  have hbX : (tensorReductionComparison l E X).hom.app (F.obj M, F.obj N) =
      SX.reduction.map (eX.hom.app (F.obj M, F.obj N)) ≫
        μX.app (F.obj M, F.obj N) := by
    exact congrArg (fun z ↦ z.app (F.obj M, F.obj N))
      (tensorReduction_eq_normalized l E d o m X eX heX)
  have hn := (m.reductionPull f).hom.naturality (eY.hom.app (M, N))
  dsimp only [Functor.comp_map] at hn
  have hp := tensorModelPullback f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
    (tensorModel l E Y) (d.tensor Y).ordinary
    (tensorModel l E X) (d.tensor X).ordinary eY eX heY heX M N
  change F.map (eY.hom.app (M, N)) ≫
    (IntegralSystemRealization.ringedTensorPull l E d f).hom.app (M, N) =
    (proEtaleCanonicalTensorComparison f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
      (tensorModel l E Y) (tensorModel l E X)).hom.app (M, N) ≫
      eX.hom.app (F.obj M, F.obj N) at hp
  have hg := IntegralSystemRealization.canonicalReductionTensorPull l E o m d f M N
  change (m.reductionPull f).hom.app ((d.tensor Y).ordinary.tensor.obj (M, N)) ≫
      P.map (μY.app (M, N)) ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (SY.reduction.obj M, SY.reduction.obj N) =
    SX.reduction.map ((IntegralSystemRealization.ringedTensorPull l E d f).hom.app (M, N)) ≫
      μX.app (F.obj M, F.obj N) ≫ SX.systemClosed.tensor.map
        (Prod.mkHom ((m.reductionPull f).hom.app M)
          ((m.reductionPull f).hom.app N)) at hg
  -- Conjugate the general square by the normalized tensor model isomorphisms.
  rw [ha, hbY, hbX]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hg]
  rw [← SX.reduction.map_comp_assoc, hp, SX.reduction.map_comp]
  simp only [Category.assoc]
  rfl

end WeilConjectures.IntegralOrdinary
