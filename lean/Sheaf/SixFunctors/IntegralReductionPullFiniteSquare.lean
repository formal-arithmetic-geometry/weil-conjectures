/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! # Finite scalar pullback in the canonical quotient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Scalar/pullback comparison fixed by the actual restriction/direct-image square.
This is a construction from adjunctions, with no chosen existence witness.
Source: Stacks 0D6D, 0D6E and 06YY
(blueprint: lem-sf-integral-reduction-pull-finite-square). -/
@[irreducible] def integralFiniteScalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ringedPull l E f ⋙ scalarReductionDerivedExtension l E X n ≅
      scalarReductionDerivedExtension l E Y n ⋙ finiteDerivedPullback l E n f :=
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let q := PurCompactSupport.scalarPull
    (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f
  Functor.isoWhiskerLeft _ (PurCompactSupport.finiteReductionIso l E X n).symm ≪≫ q ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E Y n) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n f))

/-- Finite evaluation of the whole-system pullback model is the canonical scalar square.
Source: Stacks 07A4, 07A6, 0941 and 0D6D; fix-prop-coherence, coefficient
comparisons before taking open mates
(blueprint: lem-sf-integral-reduction-pull-finite-square).

Proof: choose a flat-term K-flat representative P of H. Geometric inverse image
preserves flat terms and K-flatness, so model.model applies to P and its inverse
image. Evaluate that equation at n. The ordinary limit projection equation in
model.ordinary identifies the evaluated ordinary conjugate with quotient/pullback
interchange: after inserting the scalar units, both section maps send a section
and its quotient coefficient to the same pulled-back tensor. The unit-normalized
restriction/direct-image comparison defining integralFiniteScalarPull has that
same transpose. The reductionModel equations of the calculus and the cochain
normalization of pullbackTensorDerivedEvaluation cancel the computation
isomorphisms on both sides. This proves the displayed equation on Q(P).
Naturality and the K-flat resolution isomorphism transport it to H. No open
extension, open mate, constructibility, completeness or nonempty-scheme
hypothesis is used; zero complexes and n=0 obey the same tensor equation. -/
theorem integralReductionPullFiniteSquare (o : Operations l E)
    (model : RealizationModel l E o) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : Integral l E Y) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).map ((model.reductionPull f).hom.app H) ≫
      (pullbackTensorDerivedEvaluation l E f n).hom.app ((calculus l E Y).reduction.obj H) ≫
      (finiteDerivedPullback l E n f).map (((calculus l E Y).reductionEvaluation n).hom.app H) =
    ((calculus l E X).reductionEvaluation n).hom.app ((ringedPull l E f).obj H) ≫
      (integralFiniteScalarPull l E f n).hom.app H := by sorry

end WeilConjectures.IntegralSystemRealization
