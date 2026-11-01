/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization

/-! # Specified finite intrinsic tensor comparison

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 07A4 and 04VK.
(blueprint: def-sf-canonical-finite-intrinsic-tensor-comparison).

This exposes the actual construction previously used inside the proved pointwise
Nonempty statement in FiniteIntrinsicTensorComponent. Its value is determined by
scalar tensor descent, the coefficient counits and the intrinsic tensor model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.tensor
  sfIntrinsicDerivedEquivalence

/-- The specified constant-coefficient tensor comparison, constructed by descending the
balanced tensor map on simultaneous flat K-flat representatives and cancelling the
coefficient counits. Its value is fixed by this construction, rather than chosen from
an unnormalized existence assertion.
Source: Stacks 07A4, 04VK; fix-prop-projection-formula, same-map sentence.
(blueprint: def-sf-canonical-finite-intrinsic-tensor-comparison). -/
@[irreducible] def canonicalFiniteIntrinsicTensorComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (X : SixFunctorSpace D) :
    finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
      evaluatedTensor (C := C) (E := E) m X := by
  classical
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let F := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  let a := pullbackTensorFiniteModel C.l E X.obj.left m
  let e := finiteScalarTensorRealization X.obj.left A a
  let Tfix := CompactSupportFiniteProjection.fixedTensor (C := C) (E := E)
    (n := m + 1) X
  let preT := (((Functor.whiskeringLeft₂ _).obj F.inverse).obj F.inverse).obj Tfix
  let postpre := (Functor.postcompose₂.obj F.functor).obj preT
  let prepost := (((Functor.whiskeringLeft₂ _).obj F.inverse).obj F.inverse).obj
    ((Functor.postcompose₂.obj F.functor).obj Tfix)
  let r : postpre ≅ prepost :=
    NatIso.ofComponents
      (fun K ↦ NatIso.ofComponents (fun L ↦ Iso.refl _)
        (by intros; simp [postpre, prepost, preT])) (by
        intros
        apply NatTrans.ext
        ext
        simp [postpre, prepost, preT])
  let ePre := (((Functor.whiskeringLeft₂ _).obj F.inverse).obj F.inverse).mapIso e
  let j :
      (((Functor.whiskeringLeft₂ _).obj F.inverse).obj F.inverse).obj
          ((((Functor.whiskeringLeft₂ _).obj F.functor).obj F.functor).obj
            (Functor.curry.obj a.tensor)) ≅
        Functor.curry.obj a.tensor :=
    NatIso.ofComponents
      (fun K ↦ NatIso.ofComponents
        (fun L ↦ a.tensor.mapIso
          (Iso.prod (F.counitIso.app K) (F.counitIso.app L))) (by
          intro L L' g
          dsimp
          rw [← a.tensor.map_comp, ← a.tensor.map_comp]
          congr 1
          ext
          · simp
          · exact F.counitIso.hom.naturality g)) (by
        intro K K' f
        apply NatTrans.ext
        ext L
        dsimp
        rw [← a.tensor.map_comp, ← a.tensor.map_comp]
        congr 1
        ext
        · exact F.counitIso.hom.naturality f
        · simp)
  let eh := ePre ≪≫ j
  let ehU := Functor.uncurry.mapIso eh
  let fin := Functor.uncurry.mapIso r ≪≫ ehU ≪≫
    Functor.currying.counitIso.app a.tensor ≪≫
    pullbackTensorFiniteModelIso C.l E X.obj.left m
  exact by
    simpa [evaluatedTensor, CompactSupportFiniteProjection.tensor,
      CompactSupportFiniteProjection.realization, CompactSupportFiniteProjection.fixedTensor,
      sixFunctorFiniteRealization, F, A, a, e, ePre, j, eh, ehU, r, Tfix, preT, postpre,
      prepost, fin, integralCoefficientCommRingSheaf] using fin.symm

end WeilConjectures.IntegralProjectionReduction
