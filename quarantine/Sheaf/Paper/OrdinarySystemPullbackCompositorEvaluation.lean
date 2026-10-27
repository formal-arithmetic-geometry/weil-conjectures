/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.SixFunctors.IntegralSystemOperations

/-! # The ordinary finite evaluation square for section-normalized pullback

Source: Stacks Project, Tag 03D8, and the ordinary adjunction unit normalizations.
(blueprint: lem-pur-ordinary-system-pullback-compositor-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary evaluation commutes with the specified section-normalized compositor.
This concerns module sheaves, without complexes or derived localization.
Source: Stacks Project, Tag 03D8; steps 1 and 2 of the parent proof.
(blueprint: lem-pur-ordinary-system-pullback-compositor-evaluation).
Proof: the section equation of c identifies its direct compositor with restriction
along the canonical iterated-base-change isomorphism. Extensionality of module-sheaf
morphisms and then natural transformations proves that identification. Transpose
under the composite ordinary adjunction and use c.conjugate to identify its left
mate. The inverse-evaluation comparisons are fixed by their adjunction unit
formulas. Apply ordinaryCompositionEvaluation for the canonical sequence and
coefficient-module pullbacks: it is the equality obtained by transposing the two
paths under the finite adjunctions and restricting along that same base-change map.
The unit formulas identify its evaluation comparisons with those displayed here.
Finally the unit characterization of pullbackTensorLevelIntrinsic transports this
identity from the coefficient-module pullback to the intrinsic pullback, whose
compositor is the conjugate of the same base-change restriction. Injectivity of
adjunction hom equivalences gives the displayed ordinary square. This argument
uses arbitrary sections, so applies to zero sheaves and n=0 without exceptions;
identity scheme morphisms use the same adjunction unit equations. -/
theorem ordinarySystemPullbackCompositorEvaluation
    (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (M : coefficientSequenceModules l E Z) :
    (coefficientSequenceEvaluation l E X n).map ((c.ordinaryPull f g).hom.app M) ≫
      ((pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
        Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
          (pullbackTensorLevelIntrinsic l E f n)).hom.app
            ((pullbackTensorSequenceInverse l E g).obj M) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map
        (((pullbackTensorSequenceInverseEvaluation l E g n).symm ≪≫
          Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Z n)
            (pullbackTensorLevelIntrinsic l E g n)).hom.app M) =
    ((pullbackTensorSequenceInverseEvaluation l E (f ≫ g) n).symm ≪≫
      Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Z n)
        (pullbackTensorLevelIntrinsic l E (f ≫ g) n)).hom.app M ≫
      (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) f g).hom.app
        ((coefficientSequenceEvaluation l E Z n).obj M) := by sorry

end WeilConjectures.IntegralSystemRealization
