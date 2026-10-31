/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Whole-system pullback and tensor coordinates at the open factor

Source: prop-sf-pf-coherence.proof.md, monoidality in the mate construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction.OpenCoordinates
open IntegralSystemRealization ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

private theorem curry_counit_whisker
    {A B : Type*} [Category A] [Category B] (F : A × A ⥤ A) (R : A ⥤ B) :
    Functor.isoWhiskerRight (Functor.currying.counitIso.app F) R =
      eqToIso (congrArg (fun T ↦ T ⋙ R) (Functor.uncurry_obj_curry_obj F)) := by
  apply Iso.ext
  ext P
  simp [Functor.currying, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    eqToHom_app]

private theorem transported_inverse_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ C) (T : B ⥤ D) (G : D ⥤ C)
    {F F₀ : B ⥤ A} {TA TA₀ : A × A ⥤ A} {TB TB₀ : B × B ⥤ B}
    (hF : F₀ = F) (hA : TA₀ = TA) (hB : TB₀ = TB)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (χ : F ⋙ R ≅ T ⋙ G)
    (μA : TA ⋙ R ≅ R.prod R ⋙ TC) (μB : TB ⋙ T ≅ T.prod T ⋙ TD)
    (ψ : TD ⋙ G ≅ G.prod G ⋙ TC) (M N : B)
    (α : F₀.obj (TB₀.obj (M, N)) ≅ TA₀.obj (F₀.obj M, F₀.obj N))
    (β : F.obj (TB.obj (M, N)) ≅ TA.obj (F.obj M, F.obj N))
    (hα : HEq α.hom β.hom)
    (h : R.map β.hom ≫ μA.hom.app (F.obj M, F.obj N) ≫
        TC.map (Prod.mkHom (χ.hom.app M) (χ.hom.app N)) =
      χ.hom.app (TB.obj (M, N)) ≫ G.map (μB.hom.app (M, N)) ≫
        ψ.hom.app (T.obj M, T.obj N)) :
    let χ₀ := eqToIso (congrArg (fun F ↦ F ⋙ R) hF) ≪≫ χ
    let μA₀ := eqToIso (congrArg (fun TA ↦ TA ⋙ R) hA) ≪≫ μA
    let μB₀ := eqToIso (congrArg (fun TB ↦ TB ⋙ T) hB) ≪≫ μB
    R.map α.inv ≫ χ₀.hom.app (TB₀.obj (M, N)) ≫ G.map (μB₀.hom.app (M, N)) =
      μA₀.hom.app (F₀.obj M, F₀.obj N) ≫
        TC.map (Prod.mkHom (χ₀.hom.app M) (χ₀.hom.app N)) ≫
        ψ.inv.app (T.obj M, T.obj N) := by
  subst F₀ TA₀ TB₀
  have hα' : α = β := Iso.ext (eq_of_heq hα)
  subst α
  simp only [eqToIso_refl, Iso.refl_trans]
  apply (cancel_epi (R.map β.hom)).1
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]
  rw [reassoc_of% h]
  simp

/-- Inverse tensor/pullback commutes with the actual whole-system reduction
comparisons. Neither open extension nor either projection map occurs here.

Source: prop-sf-pf-coherence.proof.md, monoidality of pullback;
proof step 1 of lem-sf-integral-projection-open-tensor-coordinates.
(blueprint: lem-sf-integral-open-pull-tensor-reduction).

Proof: use residue Tor to put the two constructible inputs in common finite Tor
intervals, and choose simultaneous flat-term K-flat quotient representatives.
The integralOpenTensorPullbackNormalization field identifies openTensorPullback
with canonicalIntegralPullbackTensor. Its quotient normalization and the tensor
and pullback primitive augmentation formulas identify the forward comparison
with the same tensor map on strict quotient complexes on both sides. Indeed,
scalar extension followed by pullback sends a tensor x tensor y to the tensor
of the two scalar pullbacks, compatibly with the signed total differential and
all quotient transitions. Localize this equality and use naturality of the
actual reconstruction counit. This gives the forward whole-system square in
coordinates tensor and pullComparison. Conjugate by the two tensor/pullback
isomorphisms to get the inverse square below. No open adjunction, compositor,
compact support, or detection of arrows by finite evaluations is used. Zero
inputs and identity or empty opens satisfy the same tensor identity. -/
theorem integralOpenPullTensorReduction
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    (Q : SixFunctorCompactifiedSquare D)
    (M N : sfIntegralConstructibleCategory C.l E Q.Z.obj.left) :
    let A := H.integralExchange Q
    let χ := pullComparison H hl o z Q.i
    (reduce Q.X).map ((A.openTensorPullback.inv.app M).app N) ≫
        χ.hom.app (((H.integralTensor Q.Z).obj M).obj N) ≫
        (pull C.l E Q.i.hom.left).map (((tensor H hl Q.Z).app M).app N) =
      ((tensor H hl Q.X).app ((H.integral.pull Q.i).obj M)).app
          ((H.integral.pull Q.i).obj N) ≫
        (calculus C.l E Q.X.obj.left).systemClosed.tensor.map
          (Prod.mkHom (χ.hom.app M) (χ.hom.app N)) ≫
        (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
          ((reduce Q.Z).obj M, (reduce Q.Z).obj N)  := by
  let := FixProjectionCompactification.Coordinates.residueUnits hl Q.X
  let := FixProjectionCompactification.Coordinates.residueUnits hl Q.Z
  let A := H.integralExchange Q
  let F := constructibleIntegralPullback C.l E Q.i.hom.left
  let IX := (sfIntegralConstructible C.l E Q.X.obj.left).ι
  let IZ := (sfIntegralConstructible C.l E Q.Z.obj.left).ι
  let R := (calculus C.l E Q.X.obj.left).reduction
  let T := (calculus C.l E Q.Z.obj.left).reduction
  let e : integralDerivedPullback C.l E Q.i.hom.left ⋙ R ≅
      T ⋙ pull C.l E Q.i.hom.left :=
    NatIso.ofComponents
      (fun K ↦ FixProjectionCompactification.Coordinates.pullReduction D C E o z
        Q.i.hom.left K)
      (fun a ↦ ambientPull_naturality o z Q.i.hom.left a)
  let χ : F ⋙ reduce Q.X ≅ reduce Q.Z ⋙ pull C.l E Q.i.hom.left :=
    Functor.isoWhiskerLeft IZ e
  let μX : constructibleIntegralTensor C.l E Q.X.obj.left ⋙ reduce Q.X ≅
      (reduce Q.X).prod (reduce Q.X) ⋙ (calculus C.l E Q.X.obj.left).systemClosed.tensor :=
    Functor.isoWhiskerLeft (IX.prod IX)
      (FixProjectionCompactification.Coordinates.tensorReductionIso D C E Q.X.obj.left)
  let μZ : constructibleIntegralTensor C.l E Q.Z.obj.left ⋙ reduce Q.Z ≅
      (reduce Q.Z).prod (reduce Q.Z) ⋙ (calculus C.l E Q.Z.obj.left).systemClosed.tensor :=
    Functor.isoWhiskerLeft (IZ.prod IZ)
      (FixProjectionCompactification.Coordinates.tensorReductionIso D C E Q.Z.obj.left)
  have hX : Functor.uncurry.obj (H.integralTensor Q.X) =
      constructibleIntegralTensor C.l E Q.X.obj.left := by
    rw [H.integralTensorNormalization Q.X]
    exact Functor.uncurry_obj_curry_obj _
  have hZ : Functor.uncurry.obj (H.integralTensor Q.Z) =
      constructibleIntegralTensor C.l E Q.Z.obj.left := by
    rw [H.integralTensorNormalization Q.Z]
    exact Functor.uncurry_obj_curry_obj _
  have hcan : (reduce Q.X).map (canonicalIntegralPullbackTensor C.l E Q.i.hom.left M N).hom ≫
      μX.hom.app (F.obj M, F.obj N) ≫
      (calculus C.l E Q.X.obj.left).systemClosed.tensor.map
        (Prod.mkHom (χ.hom.app M) (χ.hom.app N)) =
      χ.hom.app ((constructibleIntegralTensor C.l E Q.Z.obj.left).obj (M, N)) ≫
        (pull C.l E Q.i.hom.left).map (μZ.hom.app (M, N)) ≫
        (pullbackTensorSystemComparison C.l E Q.i.hom.left).hom.app
          ((reduce Q.Z).obj M, (reduce Q.Z).obj N) := by
    simpa only [canonicalIntegralPullbackTensor_reduction, μX, μZ, χ, e, F, IX, IZ, reduce,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
      FixProjectionCompactification.Coordinates.tensorReductionIso,
      FixProjectionCompactification.Coordinates.pullReduction,
      pullbackTensorIntegralReductionTensor, pullbackTensorIntegralReductionPullback,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
      Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
      using integralComparison_reduction C.l E Q.i.hom.left M N
  have he := transported_inverse_square (reduce Q.X) (reduce Q.Z)
    (pull C.l E Q.i.hom.left) (H.integralPullback Q.i) hX hZ
    (calculus C.l E Q.X.obj.left).systemClosed.tensor
    (calculus C.l E Q.Z.obj.left).systemClosed.tensor χ μX μZ
    (pullbackTensorSystemComparison C.l E Q.i.hom.left) M N
    ((A.openTensorPullback.app M).app N)
    (canonicalIntegralPullbackTensor C.l E Q.i.hom.left M N)
    (H.integralOpenTensorPullbackNormalization Q M N) hcan
  simp only [pullComparison, χ, e, μX, μZ, IX, IZ,
    tensor, FixProjectionCompactification.Coordinates.datumTensorReduction,
    FixProjectionCompactification.Coordinates.datumTensorReductionIso,
    curry_counit_whisker, Functor.uncurry_obj_obj,
    NatIso.ofComponents_hom_app, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans_assoc,
    Category.assoc] at he ⊢
  simpa only [eqToHom_trans_assoc, Category.assoc] using he

end WeilConjectures.IntegralProjectionReduction.OpenCoordinates
