/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Descent of the native tensor square from finite integral objects

Source: Bhatt--Scholze, Remark 6.8.15; common-stage universal construction.
(blueprint: lem-sf-native-pullback-tensor-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (O : Operations l p R S) (A : At l X R) (C : At l Y S)
  (V : TensorComparison l p R S O A C)
  (a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
    ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient)

/-- The native pullback tensor square at one pair of common-stage objects.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-tensor-descent). -/
def NativePullbackTensorEquation
    (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) Y) : Prop :=
  (ContinuousRational.derivedPull p O.coefficient).map (C.tensor.hom.app (M, N)) ≫
      a.inv.app ((commonStageDerivedTensor l (PadicAlgCl l) Y).obj (M, N)) ≫
      (ordinary l X R).map (canonicalCommonStagePullbackTensor l (PadicAlgCl l) p M N).hom =
    V.tensor.hom.app ((ordinary l Y S).obj M, (ordinary l Y S).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (a.inv.app M) (a.inv.app N)) ≫
      A.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) p).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) p).obj N)

private theorem app_eq_of_iso {B D : Type*} [Category* B] [Category* D]
    {F G : B ⥤ D} (α β : F ⟶ G) {M N : B} (e : M ≅ N)
    (h : α.app N = β.app N) : α.app M = β.app M := by
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, h]

/-- Equality of the tensor square on same-field integral pairs gives equality on
all pairs of common-stage objects. Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-tensor-descent).

Proof: package the two routes as natural transformations of bifunctors. Put any pair
of objects over the compositum of their recorded coefficient fields. Raw rationalization
has unchanged objects, so each object at that field is an integral representative.
Apply the supplied finite equation there. Naturality transports this equality back
along the product of the two canonical stage isomorphisms. The image of that product
is invertible, and cancellation proves the desired component equation. Neither scalar
compatibility nor the finite completion square is assumed implicitly in this descent. -/
theorem nativePullbackTensorDescent
    (hfinite : ∀ (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K L : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y),
      let I := GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E
      let Q := sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
      NativePullbackTensorEquation l p R S O A C V a (I.obj (Q.obj K)) (I.obj (Q.obj L))) :
    ∀ M N, NativePullbackTensorEquation l p R S O A C V a M N := by
  let P := commonStageDerivedPullback l (PadicAlgCl l) p
  let JX := ordinary l X R
  let JY := ordinary l Y S
  let G := ContinuousRational.derivedPull p O.coefficient
  let TY := commonStageDerivedTensor l (PadicAlgCl l) Y
  let BX := A.closed.tensor
  intro M N
  obtain ⟨_, _, _, _, _, _, _, ⟨μ, hμ⟩, _⟩ :=
    derivedPullbackTensorIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) M.stage)
      p 0 (PadicAlgCl l)
  let left := Functor.whiskerRight C.tensor.hom G ≫
    Functor.whiskerLeft TY a.inv ≫ Functor.whiskerRight μ.hom JX
  let right := Functor.whiskerLeft (JY.prod JY) V.tensor.hom ≫
    Functor.whiskerRight (NatTrans.prod a.inv a.inv) BX ≫
    Functor.whiskerLeft (P.prod P) A.tensor.hom
  let E := Padic.finiteCoefficientCompositum l (PadicAlgCl l) M.stage N.stage
  obtain ⟨hM, hN⟩ := (Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1
    M.stage N.stage
  let stage := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) Y
  let eM := stage.isoToStage M hM
  let eN := stage.isoToStage N hN
  have hStage (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K L : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) Y) :
      let I := GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) F
      left.app (I.obj K, I.obj L) = right.app (I.obj K, I.obj L) := by
    rcases K with ⟨K⟩
    rcases L with ⟨L⟩
    have hi := hfinite F K L
    simpa only [left, right, NativePullbackTensorEquation, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.prod, Functor.prod_obj,
      G, JX, JY, P, TY, BX, sfRationalConstructibleLocalization,
      ScalarLocalization.localization, ← Iso.app_hom, hμ] using hi
  have h : left.app (M, N) = right.app (M, N) := by
    apply app_eq_of_iso left right (eM.prod eN)
    exact hStage E (M.toStage hM) (N.toStage hN)
  simpa only [left, right, NativePullbackTensorEquation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.prod, Functor.prod_obj,
    G, JX, JY, P, TY, BX, ← Iso.app_hom, hμ] using h

end WeilConjectures.AdicQbarRealization.Proper
