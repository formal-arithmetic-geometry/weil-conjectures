/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteProjectionDescentMaps
import WeilConjectures.AlgebraicGeometry.CompleteProjectionReductionSquare

/-! # Descent of the actual compact-support projection mate

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraphs (2)--(3)
(blueprint: lem-sp-complete-projection-mate-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory SheafOfModules.changeOfRings SheafOfModules.monoidalCategory
  reductionEpsilon reductionGenerator ordinaryReduction
  derivedTowerEquivalence towerEquivalence
  ringedPullComp ringedProperProjection ringedCompactificationProjection

private theorem reduction_unit_isIso (m : DescentModels l E) (T : Scheme.{u})
    (A : SpNormalizedEquivalence l E T (m.abelian T) (m.red T))
    (N : Integral l E T) (h : IntegralOnSlice.IsComplete l E T none N) :
    IsIso ((adj l E m T A).unit.app N) := by
  let := A.forgetAdditive
  let := A.forgetLimits
  let := A.forgetColimits
  have hu := A.unit_isIso N h
  let H := derivedTowerEquivalence l E T (m.abelian T)
  change IsIso ((A.adjunction.comp H.toAdjunction).unit.app N)
  rw [Adjunction.comp_unit_app]
  have hh : IsIso (H.toAdjunction.unit.app
      ((spCompletedReduction l E T (m.abelian T) (m.red T)).obj N)) := by
    change IsIso (H.unitIso.hom.app _)
    infer_instance
  let := hh
  exact IsIso.comp_isIso' hu (Functor.map_isIso
    (spCompletedTotalLimit l E T (m.abelian T))
    (H.toAdjunction.unit.app ((spCompletedReduction l E T (m.abelian T) (m.red T)).obj N)))



attribute [local irreducible] reduction totalLimit constantSheaf

private theorem projection_naturality (m : DescentModels l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M M' : Integral l E X) (K K' : Integral l E Y) (v : M ⟶ M') (w : K ⟶ K') :
    (m.integral.tensor Y).ordinary.tensor.map
        (Prod.mkHom ((integralImage l E c).map v) w) ≫
      ringedCompactificationProjection l E m.integral m.openIntegral c M' K' =
    ringedCompactificationProjection l E m.integral m.openIntegral c M K ≫
      (integralImage l E c).map ((m.integral.tensor X).ordinary.tensor.map
        (Prod.mkHom v ((ringedPull l E f).map w))) := by
  let P := ringedPush l E c.g
  let J := ringedOpen l E c.i
  let G := ringedPull l E c.g
  let TX := (m.integral.tensor X).ordinary.tensor
  let TZ := (m.integral.tensor c.Z).ordinary.tensor
  let TY := (m.integral.tensor Y).ordinary.tensor
  let a := ringedProperProjection l E m.integral c.g
  have hp := (Functor.uncurry.map a).naturality (Prod.mkHom (J.map v) w)
  dsimp [Functor.uncurry, Functor.curryObj, Functor.postcompose₂,
    Functor.whiskeringLeft₂] at hp
  simp only [← Functor.map_comp, prod_comp,
    Category.id_comp, Category.comp_id] at hp
  have ho := (m.openIntegral.projection c.i).hom.naturality
    (Prod.mkHom v (G.map w))
  dsimp only [ringedTensorLeft, ringedTensorRight, Functor.comp_map,
    Functor.prod_map, Functor.id_map] at ho
  let e (N : Integral l E Y) := (ringedPullComp l E c.i c.g).inv.app N ≫
    eqToHom (congrArg (fun g : X ⟶ Y ↦ (ringedPull l E g).obj N) c.comm.symm)
  have he0 : (ringedPull l E (c.i ≫ c.g)).map w ≫
      eqToHom (congrArg (fun g : X ⟶ Y ↦ (ringedPull l E g).obj K') c.comm.symm) =
    eqToHom (congrArg (fun g : X ⟶ Y ↦ (ringedPull l E g).obj K) c.comm.symm) ≫
      (ringedPull l E f).map w :=
    eqToHom_naturality (fun g : X ⟶ Y ↦ (ringedPull l E g).map w) c.comm.symm
  have he : (ringedPull l E c.i).map (G.map w) ≫ e K' =
      e K ≫ (ringedPull l E f).map w := by
    have hn := (ringedPullComp l E c.i c.g).inv.naturality w
    dsimp only [Functor.comp_map] at hn
    have hn' := congrArg (fun z ↦ z ≫ eqToHom
      (congrArg (fun g : X ⟶ Y ↦ (ringedPull l E g).obj K') c.comm.symm)) hn
    have he0' := congrArg (fun z ↦ (ringedPullComp l E c.i c.g).inv.app K ≫ z) he0
    calc
      _ = (ringedPullComp l E c.i c.g).inv.app K ≫
          (ringedPull l E (c.i ≫ c.g)).map w ≫ eqToHom
            (congrArg (fun g : X ⟶ Y ↦ (ringedPull l E g).obj K') c.comm.symm) := by
        simpa only [e, G, Category.assoc] using hn'
      _ = _ := by simpa only [e, Category.assoc] using he0'
  have ht : TX.map (Prod.mkHom v ((ringedPull l E c.i).map (G.map w))) ≫
      TX.map (Prod.mkHom (𝟙 _) (e K')) =
    TX.map (Prod.mkHom (𝟙 _) (e K)) ≫
      TX.map (Prod.mkHom v ((ringedPull l E f).map w)) := by
    rw [← TX.map_comp, ← TX.map_comp]
    apply congrArg TX.map
    ext
    · simp
    · exact he
  have htail := congrArg (fun z ↦
      (m.openIntegral.projection c.i).hom.app (M, G.obj K) ≫ J.map z) ht
  rw [J.map_comp, J.map_comp] at htail
  have htail' := congrArg (fun z ↦
      z ≫ J.map (TX.map (Prod.mkHom (𝟙 _) (e K')))) ho
  have htotal :
      TZ.map (Prod.mkHom (J.map v) (G.map w)) ≫
          (m.openIntegral.projection c.i).hom.app (M', G.obj K') ≫
          J.map (TX.map (Prod.mkHom (𝟙 _) (e K'))) =
        (m.openIntegral.projection c.i).hom.app (M, G.obj K) ≫
          J.map (TX.map (Prod.mkHom (𝟙 _) (e K))) ≫
          J.map (TX.map (Prod.mkHom v ((ringedPull l E f).map w))) := by
    calc
      _ = _ := by simpa only [TZ, TX, J, Functor.id_obj, Category.assoc] using htail'
      _ = _ := htail
  have htotal' := congrArg (fun z ↦ (a.app (J.obj M)).app K ≫ P.map z) htotal
  simp only [Functor.map_comp] at htotal'
  have hfinal : TY.map (Prod.mkHom (P.map (J.map v)) w) ≫
      (a.app (J.obj M')).app K' ≫ P.map
        ((m.openIntegral.projection c.i).hom.app (M', G.obj K') ≫
          J.map (TX.map (Prod.mkHom (𝟙 M') (e K')))) =
    ((a.app (J.obj M)).app K ≫ P.map
      ((m.openIntegral.projection c.i).hom.app (M, G.obj K) ≫
        J.map (TX.map (Prod.mkHom (𝟙 M) (e K))))) ≫
      P.map (J.map (TX.map (Prod.mkHom v ((ringedPull l E f).map w)))) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, ← Category.assoc, hp]
    simpa only [P, J, G, TX, TY, TZ, a, Functor.comp_obj,
      Functor.curryObj, Functor.id_obj, Category.assoc] using htotal'
  simpa only [ringedCompactificationProjection, integralImage, Functor.comp_map,
    P, J, G, TX, TY, a, e] using hfinal

variable (m : DescentModels l E)

/-- Descent of the actual proper-counit/inverse-open-unit projection mate.
Source: current blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraphs (2)--(3)
(blueprint: lem-sp-complete-projection-mate-descent).

Proof: identify reduction with the ringed sequence projection's derived pullback,
and total limit with its derived direct image. TensorReductionModel and
PullReductionModel fix the quotient augmentations and all strict transitions.
Ringed exchange/tensor coherence identifies the reduction of the proper counit
projection with its system mate. The open adjunct bijection and the normalized
openScalar inverse identify the inverse-open-unit projections before evaluation.
The defining openLimit and properLimit maps are their reduction/limit transposes.
Mate pasting and the two triangle identities identify reconstruction with proper
exchange followed by the proper image of openScalar. Pasting the proper and open
projection squares, with the normalized pullback compositor, therefore gives
red(pi) = transportedProjection. Naturality of the actual reduction unit gives
pi followed by eta_U = eta_V followed by L(red(pi)). Derived completeness makes
the actual units invertible, by the normalized reconstruction equivalence and
cofinality of ell-powers with uniformizer powers. Both system mates are invertible,
so the transported map is invertible. Conjugating its inverse by these same units
gives the asserted inverse. Every step is natural in both inputs; the final
naturality equation is the bifunctoriality square for this very projection map.
No monoidal structure on totalLimit or faithfulness of derived evaluations is used.
-/
theorem complete_projection_mate_descent
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (X Y : Over (Scheme.Spec.obj (op (CommRingCat.of k))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpNormalizedEquivalence l E X.left (m.abelian X.left) (m.red X.left))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y.left (m.abelian Y.left) (m.red Y.left))
    (M : Integral l E X.left) (K : Integral l E Y.left)
    (_hM : IntegralOnSlice.IsComplete l E X.left none M)
    (_hK : IntegralOnSlice.IsComplete l E Y.left none K)
    (_hMplus : ∃ a : ℤ, ((red l E m X.left).obj M).IsGE a)
    (_hKplus : ∃ a : ℤ, ((red l E m Y.left).obj K).IsGE a)
    (_hH : IntegralOnSlice.IsComplete l E X.left none (inputTensor l E m f.left M K))
    (_hHplus : ∃ a : ℤ, ((red l E m X.left).obj (inputTensor l E m f.left M K)).IsGE a)
    (_hU : IntegralOnSlice.IsComplete l E Y.left none
      ((integralImage l E c).obj (inputTensor l E m f.left M K)))
    (_hUplus : ∃ a : ℤ, ((red l E m Y.left).obj
      ((integralImage l E c).obj (inputTensor l E m f.left M K))).IsGE a)
    (_hV : IntegralOnSlice.IsComplete l E Y.left none
      ((m.integral.tensor Y.left).ordinary.tensor.obj ((integralImage l E c).obj M, K)))
    (_hVplus : ∃ a : ℤ, ((red l E m Y.left).obj
      ((m.integral.tensor Y.left).ordinary.tensor.obj ((integralImage l E c).obj M, K))).IsGE a)
    (_hAlphaM : IsIso (compactificationLimit l E m c AX AZ AY M))
    (_hAlphaH : IsIso (compactificationLimit l E m c AX AZ AY (inputTensor l E m f.left M K)))
    (hbM : IsIso (reconstruction l E m c AX AZ AY M))
    (hbH : IsIso (reconstruction l E m c AX AZ AY (inputTensor l E m f.left M K)))
    (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X.left).obj M)
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj ((red l E m Y.left).obj K))))
    (_hProper : IsIso (((systemProperProjection l E m c.g).app
      ((VaryingRing.J (rings l E) (transitions l E) c.i).obj ((red l E m X.left).obj M))).app
        ((red l E m Y.left).obj K))) :
    let U := (integralImage l E c).obj (inputTensor l E m f.left M K)
    let V := (m.integral.tensor Y.left).ordinary.tensor.obj ((integralImage l E c).obj M, K)
    let theta := transportedProjection l E m c AX AZ AY M K hbM hbH hOpen
    let pi := ringedCompactificationProjection l E m.integral m.openIntegral c M K
    (red l E m Y.left).map pi = theta ∧
    ∃ (etaU : U ≅ (lim l E m Y.left AY).obj ((red l E m Y.left).obj U))
      (etaV : V ≅ (lim l E m Y.left AY).obj ((red l E m Y.left).obj V))
      (t : (red l E m Y.left).obj V ≅ (red l E m Y.left).obj U) (e : V ≅ U),
      etaU.hom = (adj l E m Y.left AY).unit.app U ∧
      etaV.hom = (adj l E m Y.left AY).unit.app V ∧
      t.hom = theta ∧ e.hom = pi ∧
      pi = etaV.hom ≫ (lim l E m Y.left AY).map theta ≫ etaU.inv ∧
      e.inv = etaU.hom ≫ (lim l E m Y.left AY).map t.inv ≫ etaV.inv ∧
      ∀ (M' : Integral l E X.left) (K' : Integral l E Y.left)
        (v : M ⟶ M') (w : K ⟶ K'),
        (m.integral.tensor Y.left).ordinary.tensor.map
            (Prod.mkHom ((integralImage l E c).map v) w) ≫
          ringedCompactificationProjection l E m.integral m.openIntegral c M' K' =
        pi ≫ (integralImage l E c).map ((m.integral.tensor X.left).ordinary.tensor.map
          (Prod.mkHom v ((ringedPull l E f.left).map w))) := by
  let U := (integralImage l E c).obj (inputTensor l E m f.left M K)
  let V := (m.integral.tensor Y.left).ordinary.tensor.obj ((integralImage l E c).obj M, K)
  let theta := transportedProjection l E m c AX AZ AY M K hbM hbH hOpen
  let pi := ringedCompactificationProjection l E m.integral m.openIntegral c M K
  let := hbM
  let := hbH
  let := hOpen
  let := _hProper
  let := reduction_unit_isIso l E m Y.left AY U _hU
  let := reduction_unit_isIso l E m Y.left AY V _hV
  let etaU := asIso ((adj l E m Y.left AY).unit.app U)
  let etaV := asIso ((adj l E m Y.left AY).unit.app V)
  have ht : IsIso theta := by
    let B := (red l E m X.left).obj M
    let C := (red l E m Y.left).obj K
    let q := (VaryingRing.gComp (rings l E) (transitions l E) c.i c.g).inv.app C ≫
      eqToHom (congrArg (fun g : X.left ⟶ Y.left ↦
        (VaryingRing.G (rings l E) (transitions l E) g).obj C) c.comm.symm)
    have hq : IsIso q := by dsimp only [q]; infer_instance
    let := hq
    have hq' : IsIso ((m.systems X.left).closed.tensor.map (Prod.mkHom (𝟙 B) q)) := by
      change IsIso (((m.systems X.left).closed.tensor.mapIso
        (Iso.prod (Iso.refl B) (asIso q))).hom)
      infer_instance
    let := hq'
    have htail : IsIso ((VaryingRing.P (rings l E) (transitions l E) c.g).map
      ((@asIso _ _ _ _ (systemOpenInverse l E m c.i B
        ((VaryingRing.G (rings l E) (transitions l E) c.g).obj C)) hOpen).inv ≫
        (VaryingRing.J (rings l E) (transitions l E) c.i).map
          ((m.systems X.left).closed.tensor.map (Prod.mkHom (𝟙 B) q)))) := by
      exact Functor.map_isIso (VaryingRing.P (rings l E) (transitions l E) c.g) _
    dsimp only [theta, transportedProjection, systemProjection]
    apply IsIso.comp_isIso'
    · infer_instance
    · apply IsIso.comp_isIso'
      · exact IsIso.comp_isIso' _hProper htail
      · infer_instance
  let := ht
  let t := asIso theta
  have hred : (red l E m Y.left).map pi = theta := by
    have h := projection_reduction_square l E m c AX AZ AY M K hOpen
    have hh : (red l E m Y.left).map pi ≫
        (targetComparison l E m c AX AZ AY M K hbH).hom =
      (sourceComparison l E m c AX AZ AY M K hbM).hom ≫
        systemProjection l E m c ((red l E m X.left).obj M)
          ((red l E m Y.left).obj K) hOpen := by
      simpa only [targetComparison, sourceComparison, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, asIso_hom, Iso.refl_hom, Iso.app_hom, Category.assoc,
        Functor.map_comp] using h
    dsimp only [theta, transportedProjection]
    rw [← Category.assoc, ← hh]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hpi : pi = etaV.hom ≫ (lim l E m Y.left AY).map theta ≫ etaU.inv := by
    have h := (adj l E m Y.left AY).unit.naturality pi
    change pi ≫ etaU.hom = etaV.hom ≫ (lim l E m Y.left AY).map
      ((red l E m Y.left).map pi) at h
    rw [hred] at h
    have h' := congrArg (fun z ↦ z ≫ etaU.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'
  let e : V ≅ U := etaV ≪≫ (lim l E m Y.left AY).mapIso t ≪≫ etaU.symm
  refine ⟨hred, etaU, etaV, t, e, rfl, rfl, rfl, ?_, hpi, ?_, ?_⟩
  · exact hpi.symm
  · simp only [e, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  · intro M' K' v w
    exact projection_naturality l E m c M M' K K' v w

end AlgebraicGeometry.ProEtale.CompleteProjectionDescent
