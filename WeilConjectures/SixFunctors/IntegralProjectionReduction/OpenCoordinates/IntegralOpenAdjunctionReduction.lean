/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.OpenCoordinates.IntegralOpenProjectionCoefficientData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionOpenFactorEvaluation
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionPullEvaluation
import WeilConjectures.SixFunctors.Integral.IntegralReductionJointFaithfulness
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful

/-! # The open adjunction in whole-system coefficient coordinates

Source: prop-sf-pf-coherence.proof.md, compatibility with counits and open extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.SuppliedExchangeProjection
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction.OpenCoordinates
open IntegralSystemRealization ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  sixFunctorFinitePullback coefficientFiniteDerivedExtension
  FixProjectionCompactification.identitySquare

private theorem and_rec_eq {P Q : Prop} {A : Sort*} (f : P → Q → A) (h : P ∧ Q) :
    And.rec f h = f h.1 h.2 := by
  cases h
  rfl

private theorem iso_postcancel {A : Type*} [Category A] {X Y Z : A}
    (e : X ≅ Y) (f : Z ⟶ Y) (g : Z ⟶ X) (h : f ≫ e.inv = g) :
    f = g ≫ e.hom := by
  rw [← h, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem joint_image_ext
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B) [R.Full]
    {I : Type*} {T : I → Type*} [∀ i, Category (T i)]
    (F : ∀ i, A ⥤ T i) (V : ∀ i, B ⥤ T i) (e : ∀ i, R ⋙ V i ≅ F i)
    (hF : ∀ {K L : A} (f g : K ⟶ L), (∀ i, (F i).map f = (F i).map g) → f = g)
    {K L : A} (f g : R.obj K ⟶ R.obj L)
    (h : ∀ i, (V i).map f = (V i).map g) : f = g := by
  have hp : R.preimage f = R.preimage g := by
    apply hF
    intro i
    apply (cancel_epi ((e i).hom.app K)).1
    have hf := (e i).hom.naturality (R.preimage f)
    have hg := (e i).hom.naturality (R.preimage g)
    simp only [Functor.comp_map, Functor.map_preimage] at hf hg
    rw [← hf, ← hg, h i]
  simpa only [Functor.map_preimage] using congrArg R.map hp

private theorem inverse_mate_squares
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {U : A ⥤ C} {V : B ⥤ D}
    (χ : R ⋙ U ≅ V ⋙ R') (ρ : L ⋙ V ≅ U ⋙ L')
    (h : (mateEquiv a b).symm χ.hom = ρ.inv) :
    (∀ K, U.map (a.unit.app K) ≫ χ.hom.app (L.obj K) ≫
      R'.map (ρ.hom.app K) = b.unit.app (U.obj K)) ∧
    (∀ N, ρ.hom.app (R.obj N) ≫ L'.map (χ.hom.app N) ≫
      b.counit.app (V.obj N) = V.map (a.counit.app N)) := by
  constructor
  · intro K
    have hm := unit_mateEquiv_symm a b χ.hom K
    rw [h] at hm
    dsimp only [Functor.id_obj] at hm
    rw [← Category.assoc, hm, Category.assoc, ← R'.map_comp, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, R'.map_id, Category.comp_id]
  · intro N
    have hm := mateEquiv_counit_symm a b χ.hom N
    rw [h] at hm
    rw [hm, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem unit_composite
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {L'' : E ⥤ F} {R'' : F ⥤ E}
    (a : L ⊣ R) {U : A ⥤ C} {V : B ⥤ D} {P : C ⥤ E} {Q : D ⥤ F}
    (χ : R ⋙ U ≅ V ⋙ R') (ρ : L ⋙ V ≅ U ⋙ L')
    (ξ : R' ⋙ P ≅ Q ⋙ R'') (σ : L' ⋙ Q ≅ P ⋙ L'') (K : A) :
    P.map (U.map (a.unit.app K) ≫ χ.hom.app (L.obj K) ≫ R'.map (ρ.hom.app K)) ≫
        ξ.hom.app (L'.obj (U.obj K)) ≫ R''.map (σ.hom.app (U.obj K)) =
      P.map (U.map (a.unit.app K)) ≫ P.map (χ.hom.app (L.obj K)) ≫
        ξ.hom.app (V.obj (L.obj K)) ≫
        R''.map (Q.map (ρ.hom.app K) ≫ σ.hom.app (U.obj K)) := by
  have hn := ξ.hom.naturality (ρ.hom.app K)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private theorem evaluated_unit
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {L'' : E ⥤ F} {R'' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'')
    {U : A ⥤ C} {V : B ⥤ D} {P : C ⥤ E} {Q : D ⥤ F}
    {T : A ⥤ E} {T' : B ⥤ F}
    (χ : R ⋙ U ≅ V ⋙ R') (ρ : L ⋙ V ≅ U ⋙ L')
    (ξ : R' ⋙ P ≅ Q ⋙ R'') (σ : L' ⋙ Q ≅ P ⋙ L'')
    (e : U ⋙ P ≅ T) (e' : V ⋙ Q ≅ T')
    (γ : R ⋙ T ≅ T' ⋙ R'') (δ : L ⋙ T' ≅ T ⋙ L'')
    (hχ : ∀ N, P.map (χ.hom.app N) ≫ ξ.hom.app (V.obj N) ≫
      R''.map (e'.hom.app N) = e.hom.app (R.obj N) ≫ γ.hom.app N)
    (hρ : ∀ K, Q.map (ρ.hom.app K) ≫ σ.hom.app (U.obj K) ≫
      L''.map (e.hom.app K) = e'.hom.app (L.obj K) ≫ δ.hom.app K)
    (hb : ∀ K, P.map (b.unit.app K) ≫ ξ.hom.app (L'.obj K) ≫
      R''.map (σ.hom.app K) = c.unit.app (P.obj K))
    (hc : ∀ K, T.map (a.unit.app K) ≫ γ.hom.app (L.obj K) ≫
      R''.map (δ.hom.app K) = c.unit.app (T.obj K)) (K : A) :
    P.map (U.map (a.unit.app K) ≫ χ.hom.app (L.obj K) ≫
      R'.map (ρ.hom.app K)) = P.map (b.unit.app (U.obj K)) := by
  apply (cancel_mono (ξ.hom.app (L'.obj (U.obj K)) ≫
    R''.map (σ.hom.app (U.obj K)) ≫ R''.map (L''.map (e.hom.app K)))).1
  have hn := e.hom.naturality (a.unit.app K)
  dsimp only [Functor.comp_map] at hn
  calc
    _ = P.map (U.map (a.unit.app K)) ≫ P.map (χ.hom.app (L.obj K)) ≫
        ξ.hom.app (V.obj (L.obj K)) ≫
        R''.map (Q.map (ρ.hom.app K) ≫ σ.hom.app (U.obj K) ≫
          L''.map (e.hom.app K)) := by
      have hp := congrArg (fun v ↦ v ≫ R''.map (L''.map (e.hom.app K)))
        (unit_composite a χ ρ ξ σ K)
      simpa only [Functor.map_comp, Category.assoc] using hp
    _ = P.map (U.map (a.unit.app K)) ≫ P.map (χ.hom.app (L.obj K)) ≫
        ξ.hom.app (V.obj (L.obj K)) ≫
        R''.map (e'.hom.app (L.obj K) ≫ δ.hom.app K) := by rw [hρ]
    _ = e.hom.app K ≫ T.map (a.unit.app K) ≫ γ.hom.app (L.obj K) ≫
        R''.map (δ.hom.app K) := by
      simp only [Functor.map_comp]
      rw [reassoc_of% (hχ (L.obj K)), reassoc_of% hn]
    _ = e.hom.app K ≫ c.unit.app (T.obj K) := by rw [hc]
    _ = c.unit.app (P.obj (U.obj K)) ≫ R''.map (L''.map (e.hom.app K)) := by
      simpa only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] using
        c.unit.naturality (e.hom.app K)
    _ = _ := by rw [← hb]; simp only [Category.assoc]

private theorem composite_unit
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {L'' : E ⥤ F} {R'' : F ⥤ E}
    {a : L ⊣ R} {b : L' ⊣ R'} {c : L'' ⊣ R''}
    {U : A ⥤ C} {V : B ⥤ D} {P : C ⥤ E} {Q : D ⥤ F}
    (α : ExchangeProjectionAdjunctionComparison a b U V)
    (β : ExchangeProjectionAdjunctionComparison b c P Q) (K : A) :
    P.map (U.map (a.unit.app K)) ≫ P.map (α.right.hom.app (L.obj K)) ≫
        β.right.hom.app (V.obj (L.obj K)) ≫
        R''.map (Q.map (α.left.hom.app K) ≫ β.left.hom.app (U.obj K)) =
      c.unit.app (P.obj (U.obj K)) := by
  rw [← unit_composite a α.right α.left β.right β.left K, α.unit, β.unit]

private theorem mate_eq_of_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {U : A ⥤ C} {V : B ⥤ D}
    (χ : R ⋙ U ≅ V ⋙ R') (ρ : L ⋙ V ≅ U ⋙ L')
    (h : ∀ K, U.map (a.unit.app K) ≫ χ.hom.app (L.obj K) ≫
      R'.map (ρ.hom.app K) = b.unit.app (U.obj K)) :
    (mateEquiv a b).symm χ.hom = ρ.inv := by
  apply (mateEquiv a b).injective
  rw [Equiv.apply_symm_apply]
  ext N
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.id_obj, Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id]
  rw [← h (R.obj N)]
  simp only [TwoSquare.natTrans, Category.assoc, ← R'.map_comp_assoc,
    Functor.id_obj, Functor.comp_obj]
  simp only [Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := χ.hom.naturality (a.counit.app N)
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [← hn, ← U.map_comp_assoc, a.right_triangle_components,
    U.map_id, Category.id_comp]

private theorem reduce_image_ext
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (X : SixFunctorSpace D) {K L : sfIntegralConstructibleCategory C.l E X.obj.left}
    (f g : (reduce X).obj K ⟶ (reduce X).obj L)
    (h : ∀ m, (evaluation (C := C) (E := E) m X).map f =
      (evaluation (C := C) (E := E) m X).map g) : f = g := by
  let := FixProjectionCompactification.Coordinates.residueUnits hl X
  have hff : (reduce (C := C) (E := E) X).Full ∧
      (reduce (C := C) (E := E) X).Faithful := by
    simpa only [reduce, calculus, integralSystemReduction, pullbackTensorCalculus] using
      integralSystemReduction_fullyFaithful C.l E X.obj.left
  let := hff.1
  apply joint_image_ext (reduce X)
    (fun m ↦ reduction S m X ⋙ finiteInclusion (C := C) (E := E) m X)
    (fun m ↦ evaluation (C := C) (E := E) m X)
    (fun m ↦ Functor.isoWhiskerLeft (sfIntegralConstructible C.l E X.obj.left).ι
      ((calculus C.l E X.obj.left).reductionEvaluation m)) ?_ f g h
  intro A B a b hab
  apply integral_reductions_jointly_faithful S X a b
  intro m
  exact (finiteInclusion (C := C) (E := E) m X).map_injective (hab m)

section QuotientCoordinates
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn) (m : ℕ)
  {X Y : SixFunctorSpace D} (j : X ⟶ Y)

private def quotientOpen (hj : IsOpenImmersion j.hom.left) :=
  Functor.isoWhiskerRight ((S.integralNormalization.reduction m).openExtension j hj)
      (finiteInclusion (C := C) (E := E) m Y) ≪≫
    Functor.isoWhiskerLeft (reduction S m X) ((stage S m).finiteOpenExtension j hj)

private def quotientPull :=
  Functor.isoWhiskerRight ((S.integralNormalization.reduction m).directAdjunction j).left
      (finiteInclusion (C := C) (E := E) m X) ≪≫
    Functor.isoWhiskerLeft (reduction S m Y) ((stage S m).finitePullback j)

private def reductionIso (X : SixFunctorSpace D) :
    reduce (C := C) (E := E) X ⋙ evaluation (C := C) (E := E) m X ≅
      reduction S m X ⋙ finiteInclusion (C := C) (E := E) m X :=
  Functor.isoWhiskerLeft (sfIntegralConstructible C.l E X.obj.left).ι
    ((calculus C.l E X.obj.left).reductionEvaluation m)

end QuotientCoordinates

private theorem pull_evaluation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y) (m : ℕ)
    (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m X).map
        ((pullComparison S.higher hl o z j).hom.app N) ≫
      (pullbackTensorDerivedEvaluation C.l E j.hom.left m).hom.app ((reduce Y).obj N) ≫
      (finiteDerivedPullback C.l E m j.hom.left).map (reductionEvaluation S m Y N).hom =
    (reductionEvaluation S m X ((S.higher.integral.pull j).obj N)).hom ≫
      (quotientPull S m j).hom.app N := by
  let v := (evaluation (C := C) (E := E) m X).map
      ((pullComparison S.higher hl o z j).hom.app N) ≫
    (pullbackTensorDerivedEvaluation C.l E j.hom.left m).hom.app ((reduce Y).obj N) ≫
    (finiteDerivedPullback C.l E m j.hom.left).map (reductionEvaluation S m Y N).hom
  let w := (reductionEvaluation S m X ((S.higher.integral.pull j).obj N)).hom ≫
    (finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι.map
      (pullIso S m j N).hom
  let e := ((stage S m).finitePullback j).app ((reduction S m Y).obj N)
  have hv : v ≫ e.inv = w := by
    simpa only [v, w, e, pullComparison_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      evaluatedPull, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Category.assoc,
      reduce, Functor.comp_obj, ObjectProperty.ι_obj] using
        integralProjectionPullEvaluation S m hl o z j N
  have h := iso_postcancel e v w hv
  simpa only [v, w, e, quotientPull, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, pullIso,
    ObjectProperty.isoMk, ObjectProperty.homMk, ObjectProperty.ι_map,
    Category.assoc] using h

set_option maxHeartbeats 1000000 in
-- Elaborating the two canonical finite adjunction presentations requires this budget.
private theorem finite_unit
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (scalarReductionDerivedExtension C.l E X.obj.left m).map
        ((S.higher.integral.openAdjunction j hj).unit.app K).hom ≫
      (finiteInclusion (C := C) (E := E) m X).map
        (((S.integralNormalization.reduction m).directAdjunction j).left.hom.app
          ((S.higher.integral.openExtension j hj).obj K)) ≫
      ((stage S m).finitePullback j).hom.app
        ((reduction S m Y).obj ((S.higher.integral.openExtension j hj).obj K)) ≫
      (finiteDerivedPullback C.l E m j.hom.left).map
        ((finiteInclusion (C := C) (E := E) m Y).map
            (((S.integralNormalization.reduction m).openExtension j hj).hom.app K) ≫
          ((stage S m).finiteOpenExtension j hj).hom.app ((reduction S m X).obj K)) =
      (finiteOpenAdj C.l E j.hom.left m).unit.app
        ((scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj) := by
  let := hj
  obtain ⟨β, hβL, hβR⟩ := (stage S m).finiteOpenAdjunctionNormalization j hj
  have h := composite_unit ((S.integralNormalization.reduction m).openAdjunction j hj) β K
  rw [(S.integralNormalization.reduction m).openAdjunction_left,
    (S.integralNormalization.reduction m).openAdjunction_right, hβL, hβR] at h
  exact h

private theorem system_evaluation_unit
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) (m : ℕ) (K : System C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m X).map ((o.extension j.hom.left).adj.unit.app K) ≫
      (pullbackTensorDerivedEvaluation C.l E j.hom.left m).hom.app
        ((Operations.shriek C.l E o j.hom.left).obj K) ≫
      (finiteDerivedPullback C.l E m j.hom.left).map
        (((o.openEvaluation j.hom.left).evaluation m).hom.app K) =
      (finiteOpenAdj C.l E j.hom.left m).unit.app
        ((evaluation (C := C) (E := E) m X).obj K) := by
  let := hj
  exact (inverse_mate_squares (o.extension j.hom.left).adj
    (finiteOpenAdj C.l E j.hom.left m)
    (pullbackTensorDerivedEvaluation C.l E j.hom.left m)
    ((o.openEvaluation j.hom.left).evaluation m)
    ((o.openEvaluation j.hom.left).transpose m)).1 K

private theorem open_evaluation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) [QuasiCompact j.hom.left]
    (m : ℕ) (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m Y).map
        ((extensionComparison S hl o z j hj).hom.app K) ≫
      ((o.openEvaluation j.hom.left).evaluation m).hom.app ((reduce X).obj K) ≫
      (sfIntrinsicExtensionByZero j.hom.left
        (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategory.map
          (reductionEvaluation S m X K).hom =
    (reductionEvaluation S m Y ((S.higher.integral.openExtension j hj).obj K)).hom ≫
      (finiteInclusion (C := C) (E := E) m Y).map
        (((S.integralNormalization.reduction m).openExtension j hj).hom.app K) ≫
      ((stage S m).finiteOpenExtension j hj).hom.app ((reduction S m X).obj K) := by
  let := hj
  let c := Compactification.ofIsOpenImmersion j.hom.left
  let A := S.higher.integralExchange (FixProjectionCompactification.identitySquare j c)
  have hF : A.stage.openExtension = S.higher.integral.openExtension j hj := A.openExtension
  let t := eqToIso (congrArg (fun F ↦ (F.obj K).obj) hF)
  have ht : FixProjectionCompactification.ProjectionFactors.openReduction
      D C E n hn S hl o z j c K =
      (calculus C.l E Y.obj.left).reduction.map t.hom ≫
        (extensionComparison S hl o z j hj).hom.app K := by
    rw [extensionComparison_hom_app]
    simp only [FixProjectionCompactification.ProjectionFactors.openReduction, and_rec_eq]
    rfl
  have hf : FixProjectionCompactification.FactorEvaluation.extension
      D C E n hn S j c m K =
      (scalarReductionDerivedExtension C.l E Y.obj.left m).mapIso t ≪≫
        (quotientOpen S m j hj).app K := by rfl
  have h := FixProjectionCompactification.integralProjectionOpenFactorEvaluation
    D C E n hn S hl o z j c m K
  rw [ht, hf] at h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at h
  have he := ((calculus C.l E Y.obj.left).reductionEvaluation m).hom.naturality t.hom
  dsimp only [Functor.comp_map, coefficientFiniteDerivedExtension] at he
  erw [← reassoc_of% he] at h
  have h' := (cancel_epi ((evaluation (C := C) (E := E) m Y).map
    ((calculus C.l E Y.obj.left).reduction.map t.hom))).1 h
  dsimp only [c, Compactification.ofIsOpenImmersion] at h'
  simpa only [reductionEvaluation, quotientOpen, reduce, sfIntegralConstructible, Functor.comp_obj,
    ObjectProperty.ι_obj, Iso.app_hom, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using h'

/-- The actual integral open adjunction has the unit and counit squares for the
specified reduction comparisons. No tensor or projection map occurs here.

Source: prop-sf-pf-coherence.proof.md, compatibility with counits and j_!;
proof step 1 of lem-sf-integral-projection-open-tensor-coordinates.
(blueprint: lem-sf-integral-open-adjunction-reduction).

Proof: evaluate the specified pullback and open-extension comparisons at each
positive quotient using integralProjectionPullEvaluation and
integralProjectionOpenFactorEvaluation, respectively. The datum's finite reduction
comparison preserves its open unit; finiteOpenAdjunctionNormalization carries that
unit to the ordinary finite adjunction. OpenEvaluation.transpose and the inverse
mate unit identity give the same equation for the system adjunction. Paste the two
unary comparison squares and use naturality of reductionEvaluation to identify the
evaluated unit composites. Their common target is isomorphic to reduction of a
constructible integral object. Fullness of coherent reduction lifts both maps to
integral maps; integral_reductions_jointly_faithful identifies their lifts. This
proves the whole-system unit equation without asserting faithfulness of unrestricted
derived evaluation. The unit equation, naturality and the right triangle identity
determine the mate; the inverse mate counit identity then gives the counit equation.
The argument uses the same adjunction identities for empty and identity opens and
zero inputs. -/
theorem integralOpenAdjunctionReduction
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) [QuasiCompact j.hom.left] :
    let a := S.higher.integral.openAdjunction j hj
    let b := (o.extension j.hom.left).adj
    let χ := pullComparison S.higher hl o z j
    let ρ := extensionComparison S hl o z j hj
    (∀ K, (reduce X).map (a.unit.app K) ≫
        χ.hom.app ((S.higher.integral.openExtension j hj).obj K) ≫
        (pull C.l E j.hom.left).map (ρ.hom.app K) = b.unit.app ((reduce X).obj K)) ∧
    (∀ N, ρ.hom.app ((S.higher.integral.pull j).obj N) ≫
        (Operations.shriek C.l E o j.hom.left).map (χ.hom.app N) ≫
        b.counit.app ((reduce Y).obj N) = (reduce Y).map (a.counit.app N)) := by
  let a := S.higher.integral.openAdjunction j hj
  let b := (o.extension j.hom.left).adj
  let χ := pullComparison S.higher hl o z j
  let ρ := extensionComparison S hl o z j hj
  have hu (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
      (reduce X).map (a.unit.app K) ≫ χ.hom.app
          ((S.higher.integral.openExtension j hj).obj K) ≫
        (pull C.l E j.hom.left).map (ρ.hom.app K) = b.unit.app ((reduce X).obj K) := by
    let q := χ.app ((S.higher.integral.openExtension j hj).obj K) ≪≫
      (pull C.l E j.hom.left).mapIso (ρ.app K)
    apply (cancel_mono q.inv).1
    apply reduce_image_ext S hl X
    intro m
    have he := evaluated_unit a b (finiteOpenAdj C.l E j.hom.left m) χ ρ
      (pullbackTensorDerivedEvaluation C.l E j.hom.left m)
      ((o.openEvaluation j.hom.left).evaluation m)
      (reductionIso S m X) (reductionIso S m Y)
      (quotientPull S m j) (quotientOpen S m j hj)
      (fun N ↦ by
        simpa only [χ, reductionIso, Functor.comp_obj, ObjectProperty.ι_obj,
          Iso.app_hom, Functor.isoWhiskerLeft_hom,
          Functor.whiskerLeft_app, reductionEvaluation] using
            pull_evaluation S hl o z j m N)
      (fun M ↦ by
        simpa only [ρ, reductionIso, quotientOpen, Functor.comp_obj,
          ObjectProperty.ι_obj, Iso.app_hom, Functor.isoWhiskerLeft_hom,
          Functor.isoWhiskerRight_hom, NatTrans.comp_app,
          Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
          reductionEvaluation, Category.assoc] using
            open_evaluation S hl o z j hj m M)
      (system_evaluation_unit o j hj m)
      (fun M ↦ by
        simpa only [a, quotientPull, quotientOpen, Functor.comp_obj, Functor.comp_map,
          reduction, sixFunctorIntegralReduction, ObjectProperty.lift, ObjectProperty.ι_obj,
          ObjectProperty.ι_map, ObjectProperty.homMk, Functor.isoWhiskerLeft_hom,
          Functor.isoWhiskerRight_hom, NatTrans.comp_app,
          Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
          Category.assoc] using finite_unit S j hj m M) K
    simpa only [Functor.map_comp] using congrArg
      (fun v ↦ v ≫ (evaluation (C := C) (E := E) m X).map q.inv) he
  exact inverse_mate_squares a b χ ρ (mate_eq_of_unit a b χ ρ hu)

end WeilConjectures.IntegralProjectionReduction.OpenCoordinates
