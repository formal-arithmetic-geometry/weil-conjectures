/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalRepresentative
import all WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact

/-! # One-variable shift compatibility of the normalized finite tensor comparison

Source: Stacks 07A4 and 0FNH, parent proof Step 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ u₂
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Functor CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

section ShiftHelpers

attribute [local instance] postcompose_right_commShift precompose_right_commShift
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  Functor.mapDerivedCategory Functor.mapHomotopyCategory _root_.DerivedCategory.Qh
  Functor.leftAdjoint Adjunction.ofIsRightAdjoint

private theorem postcompose_right_commShiftIso_hom_app
    (T : C ⥤ C ⥤ C) [T.CommShift₂Int] (F : C ⥤ D) [F.CommShift ℤ] (L U : C) (n : ℤ) :
    ((((postcompose₂.obj F).obj T).flip.obj L).commShiftIso n).hom.app U =
      F.map (((T.flip.obj L).commShiftIso n).hom.app U) ≫
        (F.commShiftIso n).hom.app ((T.obj U).obj L) :=
  Functor.commShiftIso_comp_hom_app (T.flip.obj L) F n U

private theorem precompose_right_commShiftIso_hom_app
    (S : D ⥤ D ⥤ D) [S.CommShift₂Int] (F : C ⥤ D) [F.CommShift ℤ] (L U : C) (n : ℤ) :
    ((((((whiskeringLeft₂ D).obj F).obj F).obj S).flip.obj L).commShiftIso n).hom.app U =
      (S.flip.obj (F.obj L)).map ((F.commShiftIso n).hom.app U) ≫
        ((S.flip.obj (F.obj L)).commShiftIso n).hom.app (F.obj U) :=
  Functor.commShiftIso_comp_hom_app F (S.flip.obj (F.obj L)) n U

private theorem nativeComparison_eq
    {C : Type u₁} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal] :
    F.rightExact_leftDerivedTensorComparison = F.leftDerivedTensorComparison := by
  rfl

set_option maxHeartbeats 2000000 in
-- Prove the transport identity with abstract coefficient rings before specializing.
private theorem scalarModelShiftFirst {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (U V : _root_.DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))) (n : ℤ) :
    let G := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T
    let b := Adjunction.ofIsRightAdjoint
      (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
    letI : G.CommShift ℤ := b.leftAdjointCommShift ℤ
    G.map ((((curriedTensor _).flip.obj V).commShiftIso n).hom.app U) ≫
      (G.commShiftIso n).hom.app (U ⊗ V) ≫
      ((finiteScalarMonoidalModel φ T).μIso U V).inv⟦n⟧' =
    ((finiteScalarMonoidalModel φ T).μIso (U⟦n⟧) V).inv ≫
      ((G.commShiftIso n).hom.app U) ▷ G.obj V ≫
      ((((curriedTensor _).flip.obj (G.obj V)).commShiftIso n).hom.app (G.obj U)) := by
  let : Algebra A B := φ.toAlgebra
  let F := ProEtale.sheafExtendScalars φ T
  let R := sheafCompose (ProEt.topology T) (ModuleCat.restrictScalars.{u + 1} φ)
  let : F.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  let a := (ProEtale.sheafExtendScalarsAdjunction φ T).derivedAdjunction.ofNatIsoRight
    R.rightDerivedFunctorIsoMapDerivedCategory
  let G := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T
  let b : G ⊣ ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T :=
    Adjunction.ofIsRightAdjoint
      (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  let : F.leftDerivedFunctor.CommShift ℤ := a.leftAdjointCommShift ℤ
  let : G.CommShift ℤ := b.leftAdjointCommShift ℤ
  have := a.commShift_of_rightAdjoint ℤ
  have := b.commShift_of_rightAdjoint ℤ
  have := derived_counit_commShift F R (ProEtale.sheafExtendScalarsAdjunction φ T)
  let e : F.leftDerivedFunctor ≅ G := a.leftAdjointUniq b
  have : NatTrans.CommShift e.hom ℤ :=
    adjointUniq_commShift F.leftDerivedFunctor G a b
  have : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  have hnative : NatTrans.CommShift
      ((asIso F.rightExact_leftDerivedTensorComparison).hom.flipApp V) ℤ := by
    change NatTrans.CommShift (nativeRight F V) ℤ
    exact nativeRight_commShift F V
  let τ := tensorConjugate G F.leftDerivedFunctor e.symm
    (asIso F.rightExact_leftDerivedTensorComparison)
  have hτ : NatTrans.CommShift (τ.hom.flipApp V) ℤ :=
    conjugate_right_commShift G F.leftDerivedFunctor e.symm
      (asIso F.rightExact_leftDerivedTensorComparison) V
  have h := NatTrans.shift_app_comm (τ.hom.flipApp V) n U
  rw [postcompose_right_commShiftIso_hom_app, precompose_right_commShiftIso_hom_app] at h
  simp only [Category.assoc] at h
  let : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  have hmodel : finiteScalarMonoidalModel φ T =
      Functor.Monoidal.coreMonoidalTransport e := by
    unfold finiteScalarMonoidalModel
    rfl
  have hcomp (X Y) : ((finiteScalarMonoidalModel φ T).μIso X Y).inv =
      (τ.hom.app X).app Y := by
    rw [hmodel, Functor.Monoidal.coreMonoidalTransport_μIso_inv]
    rw [tensorConjugate_hom]
    simp only [asIso_hom]
    rw [nativeComparison_eq]
    rfl
  rw [hcomp, hcomp]
  exact h

end ShiftHelpers

set_option maxHeartbeats 2000000 in
-- Kernel checking the fixed-coefficient specialization compares derived-category instances.
/-- The normalized finite tensor comparison respects a shift in its first input.
Source: Stacks 07A4 and 0FNH, parent proof Step 6.
(blueprint: lem-pur-finite-tensor-shift-first).
Proof: The native right-exact derived tensor comparison commutes with shifts in
its first input and agrees definitionally with the native monoidal comparison.
The ordinary scalar adjunction determines the shift on the native left derived
functor. Uniqueness of left adjoints gives a shift-compatible comparison with the
fixed scalar functor. Conjugating the native tensor comparison along this
isomorphism yields the inverse tensorator of finiteScalarMonoidalModel. Its
first-variable CommShift equation is the displayed equation. The representative
normalization and existsUnique_finiteTensorCore identify this constructed model
with the specified finiteTensorCore. This argument applies to every integer n. -/
theorem finiteTensorShiftFirst (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u})
    (U V : _root_.DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) (n : ℤ) :
    (P.finiteTensorReduction m hm hmn T).map
        ((((curriedTensor _).flip.obj V).commShiftIso n).hom.app U) ≫
      (P.finiteTensorScalarShift m hm hmn T n).hom.app (U ⊗ V) ≫
      ((P.finiteTensorCore m hm hmn T).μIso U V).inv⟦n⟧' =
    ((P.finiteTensorCore m hm hmn T).μIso (U⟦n⟧) V).inv ≫
      ((P.finiteTensorScalarShift m hm hmn T n).hom.app U) ▷
        (P.finiteTensorReduction m hm hmn T).obj V ≫
      ((((curriedTensor _).flip.obj
          ((P.finiteTensorReduction m hm hmn T).obj V)).commShiftIso n).hom.app
        ((P.finiteTensorReduction m hm hmn T).obj U)) := by
  -- Specialize at the cached coefficient types, so the kernel compares the derived
  -- monoidal and shift structures syntactically instead of across `ULift` instances.
  let φ : P.Coefficient →+* (P.finiteReductionSetting m hm).Coefficient :=
    (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
  have hm' : P.FiniteTensorCoreNormalized m hm hmn T (finiteScalarMonoidalModel φ T) :=
    fun C D _ _ ↦ finiteScalarMonoidalModel_representative φ T C D
  have he : finiteScalarMonoidalModel φ T = P.finiteTensorCore m hm hmn T :=
    (P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.2 _ hm'
  rw [← he]
  exact scalarModelShiftFirst φ T U V n

end WeilConjectures.PurityFiniteSetting
