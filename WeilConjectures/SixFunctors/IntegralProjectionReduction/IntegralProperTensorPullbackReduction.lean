/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData

/-! # Tensor compatibility of inverse pullback reduction

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Functor
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization
open FixProjectionCompactification.Coordinates
open ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

/-- Reorient a tensor comparison square using the actual inverses of its sides. -/
private theorem inverse_square
    {A B : Type*} [Category A] [Category B] (T : A × A ⥤ B)
    {P P' Q Q' : A} {U U' V : B} (p : P ≅ P') (q : Q ≅ Q') (r : U ≅ U')
    (v : U ⟶ T.obj (P, Q)) (a : U' ⟶ V) (b : V ⟶ T.obj (P', Q'))
    (h : v ≫ T.map (Prod.mkHom p.hom q.hom) = r.hom ≫ a ≫ b) :
    a ≫ b ≫ T.map (Prod.mkHom p.inv (𝟙 Q')) ≫
        T.map (Prod.mkHom (𝟙 P) q.inv) = r.inv ≫ v := by
  apply r.eq_inv_comp.mpr
  calc
    _ = (r.hom ≫ a ≫ b) ≫ T.map (Prod.mkHom p.inv (𝟙 Q')) ≫
        T.map (Prod.mkHom (𝟙 P) q.inv) := by simp only [Category.assoc]
    _ = (v ≫ T.map (Prod.mkHom p.hom q.hom)) ≫
        T.map (Prod.mkHom p.inv (𝟙 Q')) ≫ T.map (Prod.mkHom (𝟙 P) q.inv) := by rw [h]
    _ = v := by
      simp only [Category.assoc, ← T.map_comp, prod_comp, Iso.hom_inv_id,
        Category.comp_id, Category.id_comp]
      erw [← prod_id, T.map_id, Category.comp_id]

/-- Transport of a curried comparison changes only its endpoints. -/
private theorem transported_component
    {A B : Type*} [Category A] [Category B]
    {F F' G G' : A ⥤ A ⥤ B} (hF : F = F') (hG : G' = G)
    (e : F' ≅ G') (M N : A) :
    HEq (((eqToIso hF ≪≫ e ≪≫ eqToIso hG).hom.app M).app N)
      ((e.hom.app M).app N) := by
  subst F' G'
  simp

private def normalizedTensor
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)]
    (T : sfIntegralConstructibleCategory C.l E W ⥤
      sfIntegralConstructibleCategory C.l E W ⥤ sfIntegralConstructibleCategory C.l E W)
    (hT : T = Functor.currying.inverse.obj (constructibleIntegralTensor C.l E W)) :
    Functor.uncurry.obj T ⋙ (sfIntegralConstructible C.l E W).ι ⋙
        (calculus C.l E W).reduction ≅
      (((sfIntegralConstructible C.l E W).ι ⋙ (calculus C.l E W).reduction).prod
        ((sfIntegralConstructible C.l E W).ι ⋙ (calculus C.l E W).reduction)) ⋙
          (calculus C.l E W).systemClosed.tensor :=
  eqToIso (congrArg (fun T ↦ Functor.uncurry.obj T ⋙
      (sfIntegralConstructible C.l E W).ι ⋙ (calculus C.l E W).reduction) hT) ≪≫
    Functor.isoWhiskerRight
      (Functor.currying.counitIso.app (constructibleIntegralTensor C.l E W))
      ((sfIntegralConstructible C.l E W).ι ⋙ (calculus C.l E W).reduction) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntegralConstructible C.l E W).ι.prod (sfIntegralConstructible C.l E W).ι)
      (tensorReductionIso D C E W)

private def normalizedPull
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (C.l : X.residueField x)]
    [∀ y : Y, Invertible (C.l : Y.residueField y)]
    (F : sfIntegralConstructibleCategory C.l E Y ⥤
      sfIntegralConstructibleCategory C.l E X)
    (hF : F = constructibleIntegralPullback C.l E f) :
    F ⋙ (sfIntegralConstructible C.l E X).ι ⋙ (calculus C.l E X).reduction ≅
      (sfIntegralConstructible C.l E Y).ι ⋙ (calculus C.l E Y).reduction ⋙
        pull C.l E f := by
  let R := (calculus C.l E X).reduction
  let e : integralDerivedPullback C.l E f ⋙ R ≅
      (calculus C.l E Y).reduction ⋙ pull C.l E f :=
    NatIso.ofComponents (fun K ↦ pullReduction D C E o z f K)
      (fun a ↦ ambientPull_naturality o z f a)
  exact Functor.isoWhiskerRight
      (eqToIso (congrArg (fun F ↦ F ⋙ (sfIntegralConstructible C.l E X).ι) hF)) R ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible C.l E Y).ι e

section CanonicalReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Naturality of the actual reconstruction counit reduces the conjugated comparison.
This is the categorical calculation used privately in DerivedPullbackTensorIso. -/
private theorem reduction_comparison
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (L : S ⥤ C) (A : R ⊣ L)
    (Q : D ⥤ T) (K : T ⥤ D) (B : Q ⊣ K)
    (F : D ⥤ C) (H : T ⥤ S) (U : D × D ⥤ D) (V : C × C ⥤ C)
    (J : T × T ⥤ T) (I : S × S ⥤ S)
    (a : F ≅ Q ⋙ H ⋙ L) (b : U ≅ (Q.prod Q) ⋙ J ⋙ K)
    (c : V ≅ (R.prod R) ⋙ I ⋙ L)
    (μ : J ⋙ H ≅ (H.prod H) ⋙ I) (M N : D)
    [IsIso (B.counit.app (J.obj (Q.obj M, Q.obj N)))]
    [IsIso (A.counit.app (H.obj (Q.obj M)))]
    [IsIso (A.counit.app (H.obj (Q.obj N)))] :
    R.map (a.hom.app (U.obj (M, N)) ≫
      L.map (H.map (Q.map (b.hom.app (M, N)))) ≫
      L.map (H.map (B.counit.app (J.obj (Q.obj M, Q.obj N)))) ≫
      L.map (μ.hom.app (Q.obj M, Q.obj N)) ≫
      L.map (I.map (Prod.mkHom (inv (A.counit.app (H.obj (Q.obj M))))
        (inv (A.counit.app (H.obj (Q.obj N)))))) ≫
      L.map (I.map (Prod.mkHom (R.map (a.inv.app M)) (R.map (a.inv.app N)))) ≫
      c.inv.app (F.obj M, F.obj N)) ≫
      R.map (c.hom.app (F.obj M, F.obj N)) ≫
      A.counit.app (I.obj (R.obj (F.obj M), R.obj (F.obj N))) ≫
      I.map (Prod.mkHom (R.map (a.hom.app M) ≫ A.counit.app (H.obj (Q.obj M)))
        (R.map (a.hom.app N) ≫ A.counit.app (H.obj (Q.obj N)))) =
    R.map (a.hom.app (U.obj (M, N))) ≫
      A.counit.app (H.obj (Q.obj (U.obj (M, N)))) ≫
      H.map (Q.map (b.hom.app (M, N))) ≫
      H.map (B.counit.app (J.obj (Q.obj M, Q.obj N))) ≫
      μ.hom.app (Q.obj M, Q.obj N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (c.inv.app _) (c.hom.app _), c.inv_hom_id_app, R.map_id, Category.id_comp]
  simp only [A.counit_naturality_assoc]
  simp only [← I.map_comp, CategoryTheory.prod_comp, ← R.map_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  erw [R.map_id, R.map_id]
  simp only [Category.id_comp, IsIso.inv_hom_id]
  erw [← prod_id, I.map_id, Category.comp_id]

/-- Canonical completed pullback/tensor reduces to the specified system comparison.
Source: the definitions in CompletedPullbackTensorComparison; the same calculation
as the private integralComparison_reduction of DerivedPullbackTensorIso. -/
private theorem integralComparison_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    canonicalIntegralPullbackTensor_reduction l E f M N := by
  let := ((pullbackTensorComparisonCounits l E f) M N).1
  let := ((pullbackTensorComparisonCounits l E f) M N).2.1
  let := ((pullbackTensorComparisonCounits l E f) M N).2.2
  have hh := reduction_comparison
    (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
    (pullbackTensorCalculus l E X).adjunction
    (pullbackTensorCalculus l E Y).reduction (coefficientSequenceLimit l E Y)
    (pullbackTensorCalculus l E Y).adjunction
    (integralDerivedPullback l E f) (pullbackTensorSequenceDerived l E f)
    (integralCompletedTensor l E Y) (integralCompletedTensor l E X)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorIntegralPullbackModel l E f)
    (pullbackTensorIntegralTensorModel l E Y)
    (pullbackTensorIntegralTensorModel l E X)
    (pullbackTensorSystemComparison l E f) M.obj N.obj
  unfold canonicalIntegralPullbackTensor_reduction
  dsimp only [canonicalIntegralPullbackTensor, ObjectProperty.isoMk,
    ObjectProperty.homMk, pullbackTensorIntegralReductionTensor,
    pullbackTensorIntegralReductionPullback, pullbackTensorReferenceComparison,
    Iso.trans_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Iso.prod_hom, Functor.prod_map, Functor.comp_map,
    pullbackTensorReferencePullback, pullbackTensorReferenceTensor,
    constructibleIntegralPullback, constructibleIntegralTensor,
    ObjectProperty.lift, ObjectProperty.ι_obj, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj]
  simpa only [Functor.map_comp, Category.assoc, Iso.prod_hom, Iso.symm_hom,
    Iso.app_inv, asIso_inv, Functor.comp_map, Functor.prod_map, Functor.id_obj] using hh

end CanonicalReduction

/-- The canonical reduction square, with arbitrary equal presentations of its operations. -/
private theorem normalized_reduction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (C.l : X.residueField x)]
    [∀ y : Y, Invertible (C.l : Y.residueField y)]
    (F : sfIntegralConstructibleCategory C.l E Y ⥤
      sfIntegralConstructibleCategory C.l E X)
    (TX : sfIntegralConstructibleCategory C.l E X ⥤
      sfIntegralConstructibleCategory C.l E X ⥤ sfIntegralConstructibleCategory C.l E X)
    (TY : sfIntegralConstructibleCategory C.l E Y ⥤
      sfIntegralConstructibleCategory C.l E Y ⥤ sfIntegralConstructibleCategory C.l E Y)
    (hF : F = constructibleIntegralPullback C.l E f)
    (hTX : TX = Functor.currying.inverse.obj (constructibleIntegralTensor C.l E X))
    (hTY : TY = Functor.currying.inverse.obj (constructibleIntegralTensor C.l E Y))
    (M N : sfIntegralConstructibleCategory C.l E Y)
    (v : F.obj ((TY.obj M).obj N) ⟶ (TX.obj (F.obj M)).obj (F.obj N))
    (hv : HEq v (canonicalIntegralPullbackTensor C.l E f M N).hom) :
    (calculus C.l E X).reduction.map v.hom ≫
        (normalizedTensor D C E X TX hTX).hom.app (F.obj M, F.obj N) ≫
        (calculus C.l E X).systemClosed.tensor.map
          (Prod.mkHom ((normalizedPull D C E o z f F hF).hom.app M)
            ((normalizedPull D C E o z f F hF).hom.app N)) =
      (normalizedPull D C E o z f F hF).hom.app ((TY.obj M).obj N) ≫
        (pull C.l E f).map ((normalizedTensor D C E Y TY hTY).hom.app (M, N)) ≫
        (pullbackTensorSystemComparison C.l E f).hom.app
          ((calculus C.l E Y).reduction.obj M.obj,
            (calculus C.l E Y).reduction.obj N.obj) := by
  subst F TX TY
  have hv' := eq_of_heq hv
  subst v
  have h := integralComparison_reduction C.l E f M N
  dsimp only [canonicalIntegralPullbackTensor_reduction] at h
  simp only [normalizedTensor, normalizedPull, pullbackTensorIntegralReductionTensor,
    pullbackTensorIntegralReductionPullback,
    Iso.trans_hom, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Functor.currying,
    tensorReductionIso, pullReduction, Functor.mapIso_hom, Iso.app_hom, asIso_hom,
    Category.assoc] at h ⊢
  dsimp only [Functor.comp_map]
  erw [(sfIntegralConstructible C.l E X).ι.map_id,
    (sfIntegralConstructible C.l E Y).ι.map_id]
  repeat' first
    | erw [(calculus C.l E X).reduction.map_id]
    | erw [(calculus C.l E Y).reduction.map_id]
  repeat' erw [Category.id_comp]
  exact h

/-- The inverse pullback reduction map respects tensor. This equation involves no
proper projection, direct-image counit, or compact-support comparison.

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions;
Stacks 07A4 and 0941, tensor and pullback comparisons on simultaneous quotient models.
(blueprint: lem-sf-integral-proper-tensor-pullback-reduction).

Proof: integralTensorPullbackNormalization on the proper identity square identifies
pullTensor with the canonical completed comparison, up to the prescribed equality
transports. Transport pullComparison and tensor along the datum's operation
equalities. They become exactly the canonical reduction/pullback and
reduction/tensor isomorphisms. Naturality of the actual coherent reconstruction
counits and cancellation of the completed model isomorphisms give the forward
canonical reduction square. Precompose with inverse pullComparison on the tensor and
postcompose with the tensor of the inverse components. Functoriality cancels the
forward and inverse comparison maps and gives the displayed inverse square.
Everything takes place before finite evaluation, including zero inputs and
identity proper maps. -/
theorem integralProperTensorPullbackReduction
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (M N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (pull C.l E f.hom.left).map (((tensor H hl Y).app M).app N) ≫
        (((Functor.curry.mapIso (pullbackTensorSystemComparison C.l E f.hom.left) ≪≫
          Functor.curryObjProdComp (pull C.l E f.hom.left) (pull C.l E f.hom.left)
            (calculus C.l E X.obj.left).systemClosed.tensor).hom.app
              ((reduce Y).obj M)).app ((reduce Y).obj N)) ≫
        ((Functor.curryObj (calculus C.l E X.obj.left).systemClosed.tensor).map
          ((pullComparison H hl o z f).inv.app M)).app _ ≫
        ((Functor.curryObj (calculus C.l E X.obj.left).systemClosed.tensor).obj _).map
          ((pullComparison H hl o z f).inv.app N) =
      (pullComparison H hl o z f).inv.app (((H.integralTensor Y).obj M).obj N) ≫
        (reduce X).map (((pullTensor H f).hom.app M).app N) ≫
        ((tensor H hl X).app ((H.integral.pull f).obj M)).app
          ((H.integral.pull f).obj N) := by
  let := residueUnits hl X
  let := residueUnits hl Y
  have hv : HEq (((pullTensor H f).hom.app M).app N)
      (canonicalIntegralPullbackTensor C.l E f.hom.left M N).hom := by
    exact (transported_component _ _
      (H.integralExchange (compactSupportProperSquare f)).stage.tensorPullback M N).trans
        (H.integralTensorPullbackNormalization (compactSupportProperSquare f) M N)
  have h := normalized_reduction D C E o z f.hom.left
    (H.integral.pull f) (H.integralTensor X) (H.integralTensor Y)
    (H.integralPullback f) (H.integralTensorNormalization X)
    (H.integralTensorNormalization Y) M N (((pullTensor H f).hom.app M).app N) hv
  let T := (calculus C.l E X.obj.left).systemClosed.tensor
  let p := pullComparison H hl o z f
  change (reduce X).map (((pullTensor H f).hom.app M).app N) ≫
      ((tensor H hl X).app ((H.integral.pull f).obj M)).app
        ((H.integral.pull f).obj N) ≫
      T.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
    p.hom.app (((H.integralTensor Y).obj M).obj N) ≫
      (pull C.l E f.hom.left).map (((tensor H hl Y).app M).app N) ≫
      (pullbackTensorSystemComparison C.l E f.hom.left).hom.app
        ((reduce Y).obj M, (reduce Y).obj N) at h
  simp only [Functor.curryObj, Functor.curry, Functor.curryObjProdComp,
    Iso.trans_hom, NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Functor.mapIso_hom, Category.comp_id]
  exact inverse_square T (p.app M) (p.app N)
      (p.app (((H.integralTensor Y).obj M).obj N))
      ((reduce X).map (((pullTensor H f).hom.app M).app N) ≫
        ((tensor H hl X).app ((H.integral.pull f).obj M)).app
          ((H.integral.pull f).obj N)) _ _ (by simpa only [Iso.app_hom, Category.assoc] using h)

end WeilConjectures.IntegralProjectionReduction
