/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.CompletedBaseChangeMap

/-! # Exchange and the specified completed pullback unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
open CategoryTheory
section
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  {F : C ⥤ D} {R : D ⥤ C} {P : E ⥤ H} {Q : H ⥤ E}
  {Cv B : C ⥤ E} {Cu T : D ⥤ H} {Lv : E ⥤ C} {Lu : H ⥤ D}

private lemma projection_unit (adj : F ⊣ R) (padj : P ⊣ Q)
    (χ : B ⋙ P ⟶ F ⋙ T) (K : C) :
    B.map (adj.unit.app K) ≫
      (padj.homEquiv _ _)
        (χ.app (R.obj (F.obj K)) ≫ T.map (adj.counit.app (F.obj K))) =
      padj.unit.app (B.obj K) ≫ Q.map (χ.app K) := by
  rw [← padj.homEquiv_naturality_left]
  rw [← Category.assoc]
  have hn := χ.naturality (adj.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn]
  simp only [Functor.id_obj, Category.assoc, ← T.map_comp, adj.left_triangle_components,
    T.map_id, Category.comp_id, Adjunction.homEquiv_unit]

private lemma completed_unit_transpose (adj : F ⊣ R) (padj : P ⊣ Q)
    (av : Cv ⊣ Lv) (au : Cu ⊣ Lu) (θ : Cv ⋙ P ≅ F ⋙ Cu)
    (a : Cv ⟶ B) (K : C) :
    adj.unit.app K ≫ R.map (au.unit.app (F.obj K) ≫
      Lu.map (θ.inv.app K ≫ P.map (a.app K))) ≫
      (conjugateIsoEquiv (adj.comp au) (av.comp padj) θ).hom.app (P.obj (B.obj K)) =
    av.unit.app K ≫ Lv.map (a.app K) ≫ Lv.map (padj.unit.app (B.obj K)) := by
  let c := conjugateIsoEquiv (adj.comp au) (av.comp padj) θ
  have hc : (adj.comp au).unit.app K ≫ c.hom.app ((F ⋙ Cu).obj K) =
      (av.comp padj).unit.app K ≫ (Q ⋙ Lv).map (θ.hom.app K) :=
    unit_conjugateEquiv (adj.comp au) (av.comp padj) θ.hom K
  simp only [R.map_comp, ← Category.assoc]
  rw [← Adjunction.comp_unit_app adj au K]
  simp only [Category.assoc]
  have hn := c.hom.naturality (θ.inv.app K ≫ P.map (a.app K))
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, hc]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← Lv.map_comp, ← Lv.map_comp]
  simp only [← Q.map_comp, Iso.hom_inv_id_app_assoc]
  rw [Adjunction.comp_unit_app]
  simp only [Category.assoc]
  rw [← Lv.map_comp]
  have hu := padj.unit.naturality (a.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hu]
  simp only [Lv.map_comp]

private lemma pull_unit_of_projection (adj : F ⊣ R) (padj : P ⊣ Q)
    (av : Cv ⊣ Lv) (au : Cu ⊣ Lu) (θ : Cv ⋙ P ≅ F ⋙ Cu)
    (a : Cv ⟶ B) (b : Cu ⟶ T) (χ : B ⋙ P ⟶ F ⋙ T)
    (h : ∀ M : D,
      (av.unit ≫ Functor.whiskerRight a Lv).app (R.obj M) ≫
        Lv.map ((padj.homEquiv _ _)
          (χ.app (R.obj M) ≫ T.map (adj.counit.app M))) =
      R.map ((au.unit ≫ Functor.whiskerRight b Lu).app M) ≫
        (conjugateIsoEquiv (adj.comp au) (av.comp padj) θ).hom.app (T.obj M))
    (K : C) :
    (au.unit.app (F.obj K) ≫ Lu.map (θ.inv.app K ≫ P.map (a.app K))) ≫
      Lu.map (χ.app K) = (au.unit ≫ Functor.whiskerRight b Lu).app (F.obj K) := by
  let c := conjugateIsoEquiv (adj.comp au) (av.comp padj) θ
  let ηv := av.unit ≫ Functor.whiskerRight a Lv
  let ηu := au.unit ≫ Functor.whiskerRight b Lu
  let j := au.unit.app (F.obj K) ≫ Lu.map (θ.inv.app K ≫ P.map (a.app K))
  change j ≫ Lu.map (χ.app K) = ηu.app (F.obj K)
  apply (adj.homEquiv _ _).injective
  apply (cancel_mono (c.hom.app (T.obj (F.obj K)))).1
  simp only [Adjunction.homEquiv_unit, R.map_comp, Category.assoc]
  have hc := c.hom.naturality (χ.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [hc]
  have ht := completed_unit_transpose adj padj av au θ a K
  change adj.unit.app K ≫ R.map j ≫ c.hom.app _ ≫ Lv.map (Q.map (χ.app K)) = _
  change adj.unit.app K ≫ R.map j ≫ c.hom.app _ =
    av.unit.app K ≫ Lv.map (a.app K) ≫ Lv.map (padj.unit.app (B.obj K)) at ht
  rw [reassoc_of% ht]
  rw [← h (F.obj K)]
  have hn := ηv.naturality (adj.unit.app K)
  dsimp only [ηv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.id_map, Functor.id_obj, Functor.comp_map, Functor.comp_obj] at hn
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Lv.map_comp]
  have hp := projection_unit adj padj χ K
  dsimp only [Functor.comp_obj, Functor.id_obj] at hp
  dsimp only [Functor.id_obj]
  rw [hp]

end
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem ordinaryToCompleted_reduction {U V : Scheme.{t}} (u : U ⟶ V)
    (K : d.derived V) :
    d.ordinaryToCompleted u K ≫ (completedRlim U (d.completedRing U)).map
      ((d.reductionTowerPullbackIso u).hom.app K) =
        d.completionUnit U ((d.pull u).obj K) := by
  exact pull_unit_of_projection
    (proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
      (d.integralRingIso u)) (d.towerAdjunction u)
    (d.constantRlimAdjunction V) (d.constantRlimAdjunction U)
    (d.derivedConstantPullbackIso u)
    (completedReductionAugmentation d V) (completedReductionAugmentation d U)
    (d.reductionTowerPullbackIso u).hom
    (fun M ↦ (d.towerProjection_properties u M).2.2) K

/-- The raw ordered exchange extends the ordinary ringed mate through the actual units.
Source: blueprint completion-mate comparison, steps 6--9; Stacks Tags 099N and 0E48.
(blueprint: lem-weil-pbc-completed-exchange-unit).
Proof: transpose the published towerProjection completion-unit equation through the
ordinary and tower adjunctions. Naturality of the reduction/pullback comparison and
the ordinary left triangle identity identify the projection transpose; the conjugate
constant/pullback comparison and its unit equation identify the other side. Cancellation
gives ordinaryToCompleted followed by limit of the reduction/pullback comparison equal
to the actual completion unit. Expand strict exchange and cancel H with its inverse
before applying derived limit. Apply the new unit equality, naturality of the completion
unit, and the target projection-unit equality. Naturality of directImageRlimIso inverse
and the target pullback-unit equality finish the calculation. These are equations of
strict diagrams and their derived limits, using no faithfulness of derived evaluation.
All constructions are ambient and require no properness or finite-origin witnesses. -/
theorem AdicCoefficientDatum.completedExchange_unit
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (K : d.derived X) :
    d.ordinaryToCompleted g ((d.push f).obj K) ≫ d.completedExchange sq K =
      (d.integralExchange sq).app K ≫ (d.push f').map (d.ordinaryToCompleted g' K) := by
  let L := completedRlim Y' (d.completedRing Y')
  let R := completedReductionTower Y' d
  let η : 𝟭 (d.derived Y') ⟶ R ⋙ L :=
    (d.constantRlimAdjunction Y').unit ≫
      Functor.whiskerRight (completedReductionAugmentation d Y') L
  have hn := (η.naturality ((d.integralExchange sq).app K)).symm
  change d.completionUnit Y' ((d.pull g).obj ((d.push f).obj K)) ≫
      L.map (R.map ((d.integralExchange sq).app K)) =
    (d.integralExchange sq).app K ≫
      d.completionUnit Y' ((d.push f').obj ((d.pull g').obj K)) at hn
  have hj := ordinaryToCompleted_reduction d g ((d.push f).obj K)
  have hj' := ordinaryToCompleted_reduction d g' K
  have hp := (d.towerProjection_properties f' ((d.pull g').obj K)).2.2
  unfold AdicCoefficientDatum.completedExchange
  simp only [AdicCoefficientDatum.towerV']
  rw [← Functor.map_comp_assoc]
  simp only [Iso.hom_inv_id_assoc]
  unfold AdicCoefficientDatum.towerV AdicCoefficientDatum.towerH'
  dsimp only [AdicCoefficientDatum.fourTowerCorners]
  simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  rw [hj]
  rw [Category.assoc, hn]
  simp only [Category.assoc]
  rw [reassoc_of% hp]
  have hc := (d.directImageRlimIso f').inv.naturality
    ((d.reductionTowerPullbackIso g').inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  have hi : ((d.reductionTowerPullbackIso g').symm.app K).hom =
      (d.reductionTowerPullbackIso g').inv.app K := rfl
  rw [hi]
  rw [hc]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp]
  congr 1
  apply congrArg ((d.push f').map)
  apply (cancel_mono ((completedRlim X' (d.completedRing X')).map
    ((d.reductionTowerPullbackIso g').hom.app K))).1
  have he := ((completedRlim X' (d.completedRing X')).mapIso
    ((d.reductionTowerPullbackIso g').app K)).inv_hom_id
  change (completedRlim X' (d.completedRing X')).map
      ((d.reductionTowerPullbackIso g').inv.app K) ≫
    (completedRlim X' (d.completedRing X')).map
      ((d.reductionTowerPullbackIso g').hom.app K) = 𝟙 _ at he
  rw [Category.assoc, he]
  exact (Category.comp_id (d.completionUnit X' ((d.pull g').obj K))).trans hj'.symm

end AlgebraicGeometry.Scheme
