/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import WeilConjectures.SixFunctors.IntegralDualizingFiniteProperProjection
import WeilConjectures.SixFunctors.CoefPairingProperMateEvaluation
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections

/-! # Proper projection on finite sections tests

Source: prop-asd-internal-adjunction, projection-formula step, applied in the
finite mapping comparison of prop-coef-integral-dualizing, proof paragraph 2.
(blueprint: lem-coef-system-finite-test-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
universe t a

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem system_isIso_of_evaluations
    (l : ℕ) [Fact l.Prime] (E : Type a) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{t})
    {M N : coefficientSequenceDerived l E W} (f : M ⟶ N)
    (hf : ∀ q : ℕ, IsIso ((coefficientSequenceDerivedEvaluation l E W q).map f)) :
    IsIso f := by
  obtain ⟨B⟩ := SemilinearSections.semilinearDerivedSections.{t + 1, t, a}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)
  exact B.systems.detects f hf

universe b c d va vb vc vd

private theorem properMate_isIso_of_input_iso
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
    (F : CoefPairingFrame TA TB TC TD J P R RX) (H : D)
    {M N : A} (e : M ≅ N)
    (h : IsIso (CoefPairingFrame.leftMate TC TB F.pstar P F.properAdjunction
      F.properTensor (F.sstar.obj H) (J.obj M))) :
    IsIso (CoefPairingFrame.leftMate TC TB F.pstar P F.properAdjunction
      F.properTensor (F.sstar.obj H) (J.obj N)) := by
  let flip := (Functor.flipping (C := C) (D := C) (E := B)).functor
  let w := F.properAdjunction.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TB).flip) (T_D := (Functor.curryObj TC).flip)
    (flip.map (Functor.curry.map F.properTensor.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp F.pstar F.pstar TB)).hom)
  have : IsIso ((w.app (J.obj M)).app (F.sstar.obj H)) := h
  exact NatTrans.isIso_app_app_of_iso w (J.mapIso e) (Iso.refl (F.sstar.obj H))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- The proper projection mate is invertible on a finite sections test. This
assertion has no dualizing object, trace, or exceptional Hom comparison.

Source: prop-asd-internal-adjunction, projection-formula step; Stacks 0B56,
07A6 and 0941; prop-coef-integral-dualizing, proof paragraph 2.
(blueprint: lem-coef-system-finite-test-projection).

Proof: put H equal to the representable scalar test at n. On each quotient
slice q, the proper-mate evaluation comparison supplies a finite frame and an
isomorphism from the evaluated system arrow to its finite proper mate. Apply
the finite scalar-test projection formula to the scalar complex H evaluated
at q and to the finite reduction of K. Naturality of the proper projection
transports invertibility along S.reductionEvaluation, after exact open
extension, to the finite mate with the evaluated system input. The arrow
isomorphism reflects this invertibility to the evaluated system mate. Joint
conservativity of the actual quotient-system evaluations then gives the result.
The finite scalar-test theorem accepts arbitrary scalar complexes, so this
argument includes both the supported and the zero slices of H without a
separate computation of its support. No trace or inverse limit is involved. -/
theorem integralDualizingSystem_finite_test_projection_isIso
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    IsIso (CategoryTheory.CoefPairingFrame.leftMate G.baseTensors.systemClosed.tensor
      G.compactTensors.systemClosed.tensor G.frame.pstar G.properModules.rightDerivedFunctor
      G.frame.properAdjunction G.frame.properTensor
      (G.frame.sstar.obj
        ((coefPairingEvaluationLeft l E n).obj T))
      (G.openModules.mapDerivedCategory.obj (S.reduction.obj K))) := by
  let H := (coefPairingEvaluationLeft l E n).obj T
  let M := S.reduction.obj K
  let f := CategoryTheory.CoefPairingFrame.leftMate
    G.baseTensors.systemClosed.tensor G.compactTensors.systemClosed.tensor G.frame.pstar
    G.properModules.rightDerivedFunctor G.frame.properAdjunction G.frame.properTensor
    (G.frame.sstar.obj H) (G.openModules.mapDerivedCategory.obj M)
  apply system_isIso_of_evaluations l E (Spec (.of D.k)) f
  intro q
  obtain ⟨F, hF⟩ := coefPairing_proper_mate_evaluation l E
    (finiteDualizingCompactification D X) S G q
  obtain ⟨e⟩ := hF H M
  have hp := integralDualizing_finite_scalar_test_proper_projection_isIso
    D l hl E X S G q F K hK ((coefPairingDerivedEvaluation l E q).obj H)
  have hf := properMate_isIso_of_input_iso F
    ((coefPairingDerivedEvaluation l E q).obj H)
    (((S.reductionEvaluation q).app K).symm) hp
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).2 hf

end WeilConjectures
