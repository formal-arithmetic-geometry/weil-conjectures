/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorCoherentReduction
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnit

/-! # Integral scalar extension preserves the tensor unit

Source: Stacks Project, Tags 03EL, 07A4 and 0941
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section UnitReduction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Abstract left unit square: if a faithful reduction `Q` sends `e` to the conjugate of a
reduced unit comparison `eU`, then `e` is compatible with left unitors fixed by reduction.
Source: Stacks 07A4 (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
theorem reduced_left_unit_square
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : ∀ M N, R.obj (U.obj (M, N)) ≅ J.obj (R.obj M, R.obj N))
    (b : ∀ M N, Q.obj (V.obj (M, N)) ≅ I.obj (Q.obj M, Q.obj N))
    (hb : ∀ {X X' : D} (Y : D) (f : X ⟶ X'), Q.map (V.map (Prod.mkHom f (𝟙 Y))) ≫
      (b X' Y).hom = (b X Y).hom ≫ I.map (Prod.mkHom (Q.map f) (𝟙 _)))
    (p : F ⋙ Q ≅ R ⋙ H)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, H.obj (J.obj (M, N)) ≅ I.obj (H.obj M, H.obj N))
    (hν : ∀ {X X' : S} (Y : S) (f : X ⟶ X'), H.map (J.map (Prod.mkHom f (𝟙 Y))) ≫
      (ν X' Y).hom = (ν X Y).hom ≫ I.map (Prod.mkHom (H.map f) (𝟙 _)))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ (b (F.obj M) (F.obj N)).hom ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a M N).hom ≫ (ν (R.obj M) (R.obj N)).hom)
    (oS : S) (oT : T) (lS : ∀ A, J.obj (oS, A) ⟶ A) (lT : ∀ B, I.obj (oT, B) ⟶ B)
    (hlT : ∀ {X Y : T} (f : X ⟶ Y), I.map (Prod.mkHom (𝟙 oT) f) ≫ lT Y = lT X ≫ f)
    (eU : H.obj oS ⟶ oT)
    (hU : ∀ A, (ν oS A).hom ≫ I.map (Prod.mkHom eU (𝟙 _)) ≫ lT (H.obj A) = H.map (lS A))
    (UE : C) (uE : R.obj UE ⟶ oS) (UL : D) (uL : Q.obj UL ⟶ oT)
    (e : F.obj UE ⟶ UL) (he : Q.map e ≫ uL = p.hom.app UE ≫ H.map uE ≫ eU)
    (M : C) (lE : U.obj (UE, M) ⟶ M)
    (hlE : R.map lE = (a UE M).hom ≫ J.map (Prod.mkHom uE (𝟙 _)) ≫ lS (R.obj M))
    (lL : V.obj (UL, F.obj M) ⟶ F.obj M)
    (hlL : Q.map lL = (b UL (F.obj M)).hom ≫ I.map (Prod.mkHom uL (𝟙 _)) ≫
      lT (Q.obj (F.obj M))) :
    (μ UE M).hom ≫ V.map (Prod.mkHom e (𝟙 _)) ≫ lL = F.map lE := by
  apply Q.map_injective
  apply (cancel_mono (p.hom.app M)).1
  have hp := p.hom.naturality lE
  dsimp only [Functor.comp_map, Functor.comp_obj] at hp
  rw [Functor.map_comp, Functor.map_comp, hlL, hp, hlE, H.map_comp, H.map_comp, ← hU]
  simp only [Category.assoc]
  rw [reassoc_of% (hν _ uE), ← reassoc_of% (hμ UE M)]
  have hl := hlT (p.hom.app M)
  dsimp only [Functor.comp_obj] at hl
  rw [← hl, reassoc_of% (hb _ e)]
  have key : I.map (Prod.mkHom (Q.map e) (𝟙 _)) ≫ I.map (Prod.mkHom uL (𝟙 _)) ≫
      I.map (Prod.mkHom (𝟙 _) (p.hom.app M)) =
      I.map (Prod.mkHom (p.hom.app UE) (p.hom.app M)) ≫ I.map (Prod.mkHom (H.map uE) (𝟙 _)) ≫
        I.map (Prod.mkHom eU (𝟙 _)) := by
    simp only [← I.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, he]
    simp
  rw [reassoc_of% key]

/-- Abstract right unit square, the mirror of `reduced_left_unit_square`.
Source: Stacks 07A4 (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
theorem reduced_right_unit_square
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : ∀ M N, R.obj (U.obj (M, N)) ≅ J.obj (R.obj M, R.obj N))
    (b : ∀ M N, Q.obj (V.obj (M, N)) ≅ I.obj (Q.obj M, Q.obj N))
    (hb : ∀ {Y Y' : D} (X : D) (f : Y ⟶ Y'), Q.map (V.map (Prod.mkHom (𝟙 X) f)) ≫
      (b X Y').hom = (b X Y).hom ≫ I.map (Prod.mkHom (𝟙 _) (Q.map f)))
    (p : F ⋙ Q ≅ R ⋙ H)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, H.obj (J.obj (M, N)) ≅ I.obj (H.obj M, H.obj N))
    (hν : ∀ {Y Y' : S} (X : S) (f : Y ⟶ Y'), H.map (J.map (Prod.mkHom (𝟙 X) f)) ≫
      (ν X Y').hom = (ν X Y).hom ≫ I.map (Prod.mkHom (𝟙 _) (H.map f)))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ (b (F.obj M) (F.obj N)).hom ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a M N).hom ≫ (ν (R.obj M) (R.obj N)).hom)
    (oS : S) (oT : T) (rS : ∀ A, J.obj (A, oS) ⟶ A) (rT : ∀ B, I.obj (B, oT) ⟶ B)
    (hrT : ∀ {X Y : T} (f : X ⟶ Y), I.map (Prod.mkHom f (𝟙 oT)) ≫ rT Y = rT X ≫ f)
    (eU : H.obj oS ⟶ oT)
    (hU : ∀ A, (ν A oS).hom ≫ I.map (Prod.mkHom (𝟙 _) eU) ≫ rT (H.obj A) = H.map (rS A))
    (UE : C) (uE : R.obj UE ⟶ oS) (UL : D) (uL : Q.obj UL ⟶ oT)
    (e : F.obj UE ⟶ UL) (he : Q.map e ≫ uL = p.hom.app UE ≫ H.map uE ≫ eU)
    (M : C) (ρE : U.obj (M, UE) ⟶ M)
    (hρE : R.map ρE = (a M UE).hom ≫ J.map (Prod.mkHom (𝟙 _) uE) ≫ rS (R.obj M))
    (ρL : V.obj (F.obj M, UL) ⟶ F.obj M)
    (hρL : Q.map ρL = (b (F.obj M) UL).hom ≫ I.map (Prod.mkHom (𝟙 _) uL) ≫
      rT (Q.obj (F.obj M))) :
    (μ M UE).hom ≫ V.map (Prod.mkHom (𝟙 _) e) ≫ ρL = F.map ρE := by
  apply Q.map_injective
  apply (cancel_mono (p.hom.app M)).1
  have hp := p.hom.naturality ρE
  dsimp only [Functor.comp_map, Functor.comp_obj] at hp
  rw [Functor.map_comp, Functor.map_comp, hρL, hp, hρE, H.map_comp, H.map_comp, ← hU]
  simp only [Category.assoc]
  rw [reassoc_of% (hν _ uE), ← reassoc_of% (hμ M UE)]
  have hr := hrT (p.hom.app M)
  dsimp only [Functor.comp_obj] at hr
  rw [← hr, reassoc_of% (hb _ e)]
  have key : I.map (Prod.mkHom (𝟙 _) (Q.map e)) ≫ I.map (Prod.mkHom (𝟙 _) uL) ≫
      I.map (Prod.mkHom (p.hom.app M) (𝟙 _)) =
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app UE)) ≫ I.map (Prod.mkHom (𝟙 _) (H.map uE)) ≫
        I.map (Prod.mkHom (𝟙 _) eU) := by
    simp only [← I.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, he]
    simp
  rw [reassoc_of% key]

/-- The coherent reduction of the integral tensor, as a natural isomorphism.
Source: Stacks 07A4, 0941 (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private def integralReductionTensorIso (l : ℕ) [Fact l.Prime] (D : Type u) [Field D]
    [Algebra (Padic l) D] [FiniteDimensional (Padic l) D] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l D W ⋙ integralSystemReduction l D W ≅
      (integralSystemReduction l D W).prod (integralSystemReduction l D W) ⋙
        (pullbackTensorCalculus l D W).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l D W MN.1 MN.2) (by
    intro MN PQ k
    dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, integralSystemReduction,
      constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
      counit_model_naturality
        (pullbackTensorCalculus l D W).reduction (coefficientSequenceLimit l D W)
        (pullbackTensorCalculus l D W).adjunction (integralCompletedTensor l D W)
        (((pullbackTensorCalculus l D W).reduction.prod
          (pullbackTensorCalculus l D W).reduction) ⋙
          (pullbackTensorCalculus l D W).systemClosed.tensor)
        (pullbackTensorIntegralTensorModel l D W) (Prod.mkHom k.1.hom k.2.hom))

end UnitReduction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integral scalar extension sends a reduction-normalized unit to a reduction-normalized unit,
compatibly with the integral tensor scalar comparison and with every pair of left (respectively
right) unitors fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941 (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: coherent reduction is fully faithful on the target. Conjugate the system unit
comparison of `systemScalarTensorUnit` by the coherent scalar normalization of
`integralScalarTensorCoherentReduction` and the two unit reductions, and lift it. Both unit
squares become, after reduction, the system unit squares conjugated by the same comparisons. -/
theorem integralUnitScalarExtension
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (UE : sfIntegralConstructibleCategory l E W)
    (uE : (pullbackTensorCalculus l E W).reduction.obj UE.obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit)
    (UL : sfIntegralConstructibleCategory l L W)
    (uL : (pullbackTensorCalculus l L W).reduction.obj UL.obj ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit) :
    ∃ e : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj UE ≅ UL,
      (∀ (M : sfIntegralConstructibleCategory l E W)
        (lE : (constructibleIntegralTensor l E W).obj (UE, M) ≅ M)
        (_ : (pullbackTensorCalculus l E W).reduction.map lE.hom.hom =
          (pullbackTensorIntegralReductionTensor l E W UE M).hom ≫
            (pullbackTensorCalculus l E W).systemClosed.tensor.map (Prod.mkHom uE.hom (𝟙 _)) ≫
            ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
              ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom)
        (lL : (constructibleIntegralTensor l L W).obj (UL, (sfConstructibleIntegralScalarExtension
          0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M) ≅
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        (_ : (pullbackTensorCalculus l L W).reduction.map lL.hom.hom =
          (pullbackTensorIntegralReductionTensor l L W UL _).hom ≫
            (pullbackTensorCalculus l L W).systemClosed.tensor.map (Prod.mkHom uL.hom (𝟙 _)) ≫
            ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
              ((pullbackTensorCalculus l L W).reduction.obj
                ((sfConstructibleIntegralScalarExtension 0 l
                  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M).obj)).hom),
        (integralTensorScalarComparison l E L ι W UE M).hom ≫
          (constructibleIntegralTensor l L W).map (Prod.mkHom e.hom (𝟙 _)) ≫ lL.hom =
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map lE.hom) ∧
      (∀ (M : sfIntegralConstructibleCategory l E W)
        (ρE : (constructibleIntegralTensor l E W).obj (M, UE) ≅ M)
        (_ : (pullbackTensorCalculus l E W).reduction.map ρE.hom.hom =
          (pullbackTensorIntegralReductionTensor l E W M UE).hom ≫
            (pullbackTensorCalculus l E W).systemClosed.tensor.map (Prod.mkHom (𝟙 _) uE.hom) ≫
            ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
              ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom)
        (ρL : (constructibleIntegralTensor l L W).obj ((sfConstructibleIntegralScalarExtension
          0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M, UL) ≅
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        (_ : (pullbackTensorCalculus l L W).reduction.map ρL.hom.hom =
          (pullbackTensorIntegralReductionTensor l L W _ UL).hom ≫
            (pullbackTensorCalculus l L W).systemClosed.tensor.map (Prod.mkHom (𝟙 _) uL.hom) ≫
            ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
              ((pullbackTensorCalculus l L W).reduction.obj
                ((sfConstructibleIntegralScalarExtension 0 l
                  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M).obj)).hom),
        (integralTensorScalarComparison l E L ι W M UE).hom ≫
          (constructibleIntegralTensor l L W).map (Prod.mkHom (𝟙 _) e.hom) ≫ ρL.hom =
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map ρE.hom) := by
  let SE := pullbackTensorCalculus l E W
  let SL := pullbackTensorCalculus l L W
  let R := (sfIntegralConstructible l E W).ι ⋙ SE.reduction
  let Q := (sfIntegralConstructible l L W).ι ⋙ SL.reduction
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let σ := ScalarExtensionTower.derivedSigma l E L ι W SE SL
  let bL := integralReductionTensorIso l L W
  obtain ⟨p, hp⟩ := integralScalarTensorCoherentReduction l E L ι W
  obtain ⟨eU, hU⟩ := systemScalarTensorUnit l E L ι W
  obtain ⟨hfull, hfaith⟩ : Q.Full ∧ Q.Faithful := integralSystemReduction_fullyFaithful l L W
  let ff := Functor.FullyFaithful.ofFullyFaithful Q
  let e := ff.preimageIso (p.app UE ≪≫ H.mapIso uE ≪≫ eU ≪≫ uL.symm)
  have he : Q.map e.hom ≫ uL.hom = p.hom.app UE ≫ H.map uE.hom ≫ eU.hom := by
    simp [e]
  let _ := SE.systemClosed.monoidal
  let _ := SL.systemClosed.monoidal
  refine ⟨e, ?_, ?_⟩
  · intro M lE hlE lL hlL
    open MonoidalCategory in
    exact reduced_left_unit_square (S := coefficientSequenceDerived l E W)
      (T := coefficientSequenceDerived l L W) R Q F H (constructibleIntegralTensor l E W)
      (constructibleIntegralTensor l L W) SE.systemClosed.tensor SL.systemClosed.tensor
      (pullbackTensorIntegralReductionTensor l E W) (pullbackTensorIntegralReductionTensor l L W)
      (fun Y f ↦ by
        have h := bL.hom.naturality (Prod.mkHom f (𝟙 Y))
        dsimp only [Functor.comp_map, Functor.prod_map] at h
        rw [CategoryTheory.Functor.map_id] at h
        exact h)
      p (integralTensorScalarComparison l E L ι W) (fun A B ↦ σ.app (A, B))
      (fun Y f ↦ by
        have h := σ.hom.naturality (Prod.mkHom f (𝟙 Y))
        dsimp only [Functor.comp_map, Functor.prod_map] at h
        rw [CategoryTheory.Functor.map_id] at h
        exact h)
      hp _ _ (fun A ↦ (λ_ A).hom) (fun B ↦ (λ_ B).hom)
      (fun f ↦ by
        have h := leftUnitor_naturality f
        rw [← id_tensorHom] at h
        exact h)
      eU.hom (fun A ↦ (hU A).1) UE uE.hom UL uL.hom e.hom he M lE.hom hlE lL.hom hlL
  · intro M ρE hρE ρL hρL
    open MonoidalCategory in
    exact reduced_right_unit_square (S := coefficientSequenceDerived l E W)
      (T := coefficientSequenceDerived l L W) R Q F H (constructibleIntegralTensor l E W)
      (constructibleIntegralTensor l L W) SE.systemClosed.tensor SL.systemClosed.tensor
      (pullbackTensorIntegralReductionTensor l E W) (pullbackTensorIntegralReductionTensor l L W)
      (fun X f ↦ by
        have h := bL.hom.naturality (Prod.mkHom (𝟙 X) f)
        dsimp only [Functor.comp_map, Functor.prod_map] at h
        rw [CategoryTheory.Functor.map_id] at h
        exact h)
      p (integralTensorScalarComparison l E L ι W) (fun A B ↦ σ.app (A, B))
      (fun X f ↦ by
        have h := σ.hom.naturality (Prod.mkHom (𝟙 X) f)
        dsimp only [Functor.comp_map, Functor.prod_map] at h
        rw [CategoryTheory.Functor.map_id] at h
        exact h)
      hp _ _ (fun A ↦ (ρ_ A).hom) (fun B ↦ (ρ_ B).hom)
      (fun f ↦ by
        have h := rightUnitor_naturality f
        rw [← tensorHom_id] at h
        exact h)
      eU.hom (fun A ↦ (hU A).2) UE uE.hom UL uL.hom e.hom he M ρE.hom hρE ρL.hom hρL

end WeilConjectures
