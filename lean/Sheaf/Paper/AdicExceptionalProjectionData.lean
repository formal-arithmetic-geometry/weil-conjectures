/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.AdicExceptionalOperations
public import Mathlib.CategoryTheory.Functor.Currying

/-! # The canonical completed projection map
Source: Bhatt--Scholze Lemma 6.7.14
(blueprint: def-per-adic-exceptional-projection-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.AdicExceptionalProjection

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
  (c : Compactification (arrow f))

/-- Compact support of the tensor with completed pullback.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
def projectionSource : C l E X × C l E Y ⥤ C l E Y :=
  (𝟭 (C l E X)).prod (pull l E f) ⋙ tensor l E X ⋙ support l E f c

/-- Tensor of compact support with the target input.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
def projectionTarget : C l E X × C l E Y ⥤ C l E Y :=
  (support l E f c).prod (𝟭 (C l E Y)) ⋙ tensor l E Y

/-- First-slot tensor shift is the restriction of the unsigned K-flat/Roos comparison.
Source: Stacks 011G, 0941 (blueprint: def-per-adic-exceptional-projection-data). -/
def tensorFirstShift (W : Spaces k) (K M : C l E W) (r : ℤ) :
    (tensor l E W).obj (K⟦r⟧, M) ≅ ((tensor l E W).obj (K, M))⟦r⟧ :=
  (sfIntegralConstructible l E.carrier W.scheme).isoMk
    ((integralCompletedTensor l E.carrier W.scheme).mapIso
      (Iso.prod (((sfIntegralConstructible l E.carrier W.scheme).ι.commShiftIso r).app K)
        (Iso.refl M.obj)) ≪≫
      ((IntegralSystemRealization.tensorShifts l E.carrier).integralLeft
        W.scheme r).app (K.obj, M.obj) ≪≫
      (((sfIntegralConstructible l E.carrier W.scheme).ι.commShiftIso r).app
        ((tensor l E W).obj (K, M))).symm)

/-- Second-slot tensor shift retains the signed K-flat/Roos comparison.
Source: Stacks 011G, 0941 (blueprint: def-per-adic-exceptional-projection-data). -/
def tensorSecondShift (W : Spaces k) (K M : C l E W) (r : ℤ) :
    (tensor l E W).obj (K, M⟦r⟧) ≅ ((tensor l E W).obj (K, M))⟦r⟧ :=
  (sfIntegralConstructible l E.carrier W.scheme).isoMk
    ((integralCompletedTensor l E.carrier W.scheme).mapIso
      (Iso.prod (Iso.refl K.obj)
        (((sfIntegralConstructible l E.carrier W.scheme).ι.commShiftIso r).app M)) ≪≫
      ((IntegralSystemRealization.tensorShifts l E.carrier).integralRight
        W.scheme r).app (K.obj, M.obj) ≪≫
      (((sfIntegralConstructible l E.carrier W.scheme).ι.commShiftIso r).app
        ((tensor l E W).obj (K, M))).symm)

/-- Source shift in K: the fixed first tensor shift, followed by support's fixed shift.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
def projectionSourceFirst (K : C l E X) (M : C l E Y) (r : ℤ) :
    (projectionSource l E f c).obj (K⟦r⟧, M) ≅
      ((projectionSource l E f c).obj (K, M))⟦r⟧ :=
  (support l E f c).mapIso (tensorFirstShift l E X K ((pull l E f).obj M) r) ≪≫
    (Functor.commShiftIso (support l E f c) (self := supportShift l E f c) r).app _

/-- Target shift in K: support's fixed shift and then the fixed first tensor shift.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
def projectionTargetFirst (K : C l E X) (M : C l E Y) (r : ℤ) :
    (projectionTarget l E f c).obj (K⟦r⟧, M) ≅
      ((projectionTarget l E f c).obj (K, M))⟦r⟧ :=
  (tensor l E Y).mapIso
      (Iso.prod ((Functor.commShiftIso (support l E f c)
        (self := supportShift l E f c) r).app K) (Iso.refl M)) ≪≫
    tensorFirstShift l E Y ((support l E f c).obj K) M r

/-- Source shift in M, retaining pullback's shift and the signed second tensor shift.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
def projectionSourceSecond (K : C l E X) (M : C l E Y) (r : ℤ) :
    (projectionSource l E f c).obj (K, M⟦r⟧) ≅
      ((projectionSource l E f c).obj (K, M))⟦r⟧ :=
  (support l E f c).mapIso
      ((tensor l E X).mapIso
        (Iso.prod (Iso.refl K) ((Functor.commShiftIso (pull l E f)
          (self := pullShift l E f) r).app M)) ≪≫
        tensorSecondShift l E X K ((pull l E f).obj M) r) ≪≫
    (Functor.commShiftIso (support l E f c) (self := supportShift l E f c) r).app _

/-- Target shift in M is exactly the signed second tensor shift.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
def projectionTargetSecond (K : C l E X) (M : C l E Y) (r : ℤ) :
    (projectionTarget l E f c).obj (K, M⟦r⟧) ≅
      ((projectionTarget l E f c).obj (K, M))⟦r⟧ :=
  tensorSecondShift l E Y ((support l E f c).obj K) M r

/-- The completed projection, with its ordinary-to-completed unit equation.
The representative normalization in OpenFactorCoherence.Tensor fixes both augmentations.
The right side uses the actual proper-counit/open tensor word. Thus this condition
specifies the full derived morphism, rather than its finite evaluations alone.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-projection-data). -/
structure Projection (O : Operation l E f c)
    (T : ∀ W : Scheme.{u}, OpenFactorCoherence.Tensor l E.carrier W) where
  iso : projectionSource l E f c ≅ projectionTarget l E f c
  normalization : ∀ (K : C l E X) (M : C l E Y),
    let R := PurCompactSupport.completed l E.carrier
    let e := sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) c
    (T Y.scheme).ordinary.tensor.map (Prod.mkHom (e.hom.app K) (𝟙 M.obj)) ≫
        (OpenFactorCoherence.Tensor.chi l E.carrier (T Y.scheme)).app
          (((support l E f c).obj K).obj, M.obj) ≫
        (iso.inv.app (K, M)).hom =
      (((PurCompactSupport.projectionMap R c
        (T X.scheme).ordinary (T c.Z).ordinary (T Y.scheme).ordinary
        (PurCompactSupport.completedPull_comp l E.carrier c.i c.g)).app K.obj).app M.obj) ≫
      (PurCompactSupport.image R c).map
        ((T X.scheme).ordinary.tensor.map (Prod.mkHom (𝟙 K.obj)
          ((OpenFactorCoherence.Pull.unit l E.carrier O.pullModel).app M.obj)) ≫
          (OpenFactorCoherence.Tensor.chi l E.carrier (T X.scheme)).app
            (K.obj, ((pull l E f).obj M).obj)) ≫
      e.hom.app ((tensor l E X).obj (K, (pull l E f).obj M))
  secondShift : ∀ (K : C l E X) (M : C l E Y) (r : ℤ),
    iso.hom.app (K, M⟦r⟧) ≫ (projectionTargetSecond l E f c K M r).hom =
      (projectionSourceSecond l E f c K M r).hom ≫ (iso.hom.app (K, M))⟦r⟧'
  firstShift : ∀ (K : C l E X) (M : C l E Y) (r : ℤ),
    iso.hom.app (K⟦r⟧, M) ≫ (projectionTargetFirst l E f c K M r).hom =
      (projectionSourceFirst l E f c K M r).hom ≫ (iso.hom.app (K, M))⟦r⟧'

end WeilConjectures.AdicExceptionalProjection
