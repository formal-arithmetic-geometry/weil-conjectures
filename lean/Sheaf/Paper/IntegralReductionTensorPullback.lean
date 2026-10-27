/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.IntegralTensorReductionAugmentation
public import Sheaf.Paper.IntegralPullbackReductionAugmentation
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback

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
          ((pullbackReductionComparison l E f).hom.app N)) := by sorry

end WeilConjectures.IntegralOrdinary
