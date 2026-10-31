/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionReductionData
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionFiniteEvaluation
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProperProjectionSystemNormalization
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionReductionNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization

/-! # Normalized reduction of the individual integral tensor and projection maps

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
(blueprint: lem-sf-integral-projection-reduction-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open IntegralProjectionReduction

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.component compactSupportProjectionComponent
  compactSupportProperProjection

/-- Pasting a commuting square through its four endpoint comparisons. -/
private theorem evaluation_rectangle {A : Type*} [Category A]
    {a b c d a' b' c' d' : A}
    (ra : a ≅ a') (rb : b ≅ b') (sc : c ≅ c') (td : d ≅ d')
    {p : a ⟶ b} {p' : a' ⟶ b'} {s : a ⟶ c} {s' : a' ⟶ c'}
    {t : b ⟶ d} {t' : b' ⟶ d'} {q : c ⟶ d} {q' : c' ⟶ d'}
    (hn : p ≫ rb.hom = ra.hom ≫ p')
    (hs : s ≫ sc.hom = ra.hom ≫ s')
    (ht : t ≫ td.hom = rb.hom ≫ t')
    (hq : q ≫ td.hom = sc.hom ≫ q') (h : s ≫ q = p ≫ t) :
    p' ≫ t' = s' ≫ q' := by
  apply (cancel_epi ra.hom).1
  rw [← Category.assoc, ← hn, Category.assoc, ← ht,
    ← Category.assoc, ← h, Category.assoc, hq,
    ← Category.assoc, hs, Category.assoc]

/-- Remove the proper-identity conjugations after a projection square is transported. -/
private theorem proper_rectangle {A : Type*} [Category A]
    {a a' b b' c c' d d' : A}
    (ia : a ≅ a') (ib : b ≅ b') (ic : c ≅ c') (id : d ≅ d')
    {p : a' ⟶ b'} {q : c ⟶ d} {s : a ⟶ c} {t : b ⟶ d}
    {s' : a' ⟶ c'} {t' : b' ⟶ d'}
    (hs : ia.hom ≫ s' = s ≫ ic.hom)
    (ht : ib.hom ≫ t' = t ≫ id.hom)
    (h : ia.hom ≫ p ≫ ib.inv ≫ t = s ≫ q) :
    p ≫ t' = s' ≫ ic.inv ≫ q ≫ id.hom := by
  have h' := congrArg (fun k ↦ k ≫ id.hom) h
  simp only [Category.assoc] at h'
  rw [← ht, Iso.inv_hom_id_assoc] at h'
  apply (cancel_epi ia.hom).1
  rw [reassoc_of% hs, Iso.hom_inv_id_assoc]
  exact h'

set_option maxHeartbeats 2000000 in
-- Checking the normalized operation-coordinate types exceeds the default heartbeat budget.
/-- Reduction has natural tensor coordinates which identify each individual compactified
projection and each proper counit projection with its finite-stage map. These squares refer
to the specified adjunction comparisons; they assert no composition or pentagon equation.

Source: prop-sf-pf-reduction and the successive-reduction sentence of
fix-prop-projection-formula.proof.md; the tensor/counit normalization in
lem-sf-integral-stage-projection-reduction.
(blueprint: lem-sf-integral-projection-reduction-coordinates).

Proof: realize the whole coefficient-system operations. Apply finite evaluation of their
normalized tensor and projection expression, and take the components of its natural
isomorphism as the tensor coordinates. Naturality on the product category at (a,id) and
(id,b) proves both input naturality equations. Integral residue Tor supplies the input
condition for the existing whole-system compactification square. Evaluate that square,
paste the two endpoint comparisons and the evaluated system-projection identity, and use
naturality of the reduction/evaluation comparison. Cancel its source isomorphism; the full
finite inclusion is faithful, giving the requested finite square. For the proper map use
the whole-system proper counit normalization at the identity-open compactification and the
same evaluation argument. Tensor naturality and the coefficient comparison's properIdentity
equation identify the source coordinate change. That equation on the tensor/pullback input,
and naturality of finite properIdentity, identify the target coordinate change. Cancel the
proper-identity conjugations. The remaining finite conjugate is exactly properComponent.
This uses neither joint faithfulness of arbitrary system evaluation nor the integral
proper-coincidence law of a downstream consumer. All existential witnesses occur locally in
this proof; no definition chooses data from a mere existence assertion. -/
theorem integralProjection_reduction_coordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (m : ℕ) :
    ∃ t : TensorCoordinates d m,
      (∀ (X : SixFunctorSpace D)
        (K K' L : sfIntegralConstructibleCategory C.l E X.obj.left) (a : K ⟶ K'),
        (reduction d m X).map (((d.higher.integralTensor X).map a).app L) ≫
            (t X K' L).hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).map
              ((reduction d m X).map a)).app ((torReduction d m X).obj L)) ∧
      (∀ (X : SixFunctorSpace D)
        (K L L' : sfIntegralConstructibleCategory C.l E X.obj.left) (b : L ⟶ L'),
        (reduction d m X).map (((d.higher.integralTensor X).obj K).map b) ≫
            (t X K L').hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
              ((reduction d m X).obj K)).map ((torReduction d m X).map b)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProjectionComponent d.higher.integralExchange f c K L) ≫
            (targetIso d m t f c K L).hom =
          (sourceIso d m t f c K L).hom ≫
            CompactSupportFiniteProjection.component (stage d m) f c
              ((reduction d m X).obj K) ((torReduction d m Y).obj L)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProperProjection d.higher.integralExchange f K L) ≫
            (properTargetIso d m t f K L).hom =
          (properSourceIso d m t f K L).hom ≫
            CompactSupportFiniteProjection.properComponent (stage d m) f
              ((reduction d m X).obj K) ((torReduction d m Y).obj L)) := by
  let hl := PurCompactSupport.coefficientPrimeUnit C.l D C.different
  obtain ⟨o, ⟨z⟩⟩ := IntegralSystemRealization.integralCompactificationSystemRealization
    C.l E D C.different
  obtain ⟨e, he⟩ := integralProjectionFiniteEvaluation d m hl o z
  let t := tensorCoordinates d m e
  have hn₁ : ∀ (X : SixFunctorSpace D)
      (K K' L : sfIntegralConstructibleCategory C.l E X.obj.left)
      (a : K ⟶ K'),
      (reduction d m X).map (((d.higher.integralTensor X).map a).app L) ≫
          (t X K' L).hom =
        (t X K L).hom ≫
          ((CompactSupportFiniteProjection.partialTensor (stage d m) X).map
            ((reduction d m X).map a)).app ((torReduction d m X).obj L) := by
    intro X K K' L a
    simpa [t, tensorCoordinates, Functor.uncurry] using
      (e X).hom.naturality (Prod.mkHom a (𝟙 L))
  have hn₂ : ∀ (X : SixFunctorSpace D)
      (K L L' : sfIntegralConstructibleCategory C.l E X.obj.left)
      (b : L ⟶ L'),
      (reduction d m X).map (((d.higher.integralTensor X).obj K).map b) ≫
          (t X K L').hom =
        (t X K L).hom ≫
          ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
            ((reduction d m X).obj K)).map ((torReduction d m X).map b) := by
    intro X K L L' b
    simpa [t, tensorCoordinates, Functor.uncurry] using
      (e X).hom.naturality (Prod.mkHom (𝟙 K) b)
  refine ⟨t, hn₁, hn₂, ?_, ?_⟩
  · intro X Y f _ _ _ c K L
    let := FixProjectionCompactification.Coordinates.residueUnits hl Y
    have hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj := by
      rw [← (integral_residue_tor D C.l C.different E Y.obj.left).2]
      exact L.property
    obtain ⟨s, r, hs, hr, hp⟩ := he f c K L
    have hsys := FixProjectionCompactification.integralProjectionReductionNormalization
      D C E n hn d hl o z f c K L hL
    have hpdef :
        (d.higher.integralExchange
          (FixProjectionCompactification.identitySquare f c)).projectionComponent K L =
          compactSupportProjectionComponent d.higher.integralExchange f c K L := by
      unfold compactSupportProjectionComponent
      rfl
    rw [hpdef] at hsys
    let ev := evaluation (C := C) (E := E) m Y
    let I := finiteInclusion (C := C) (E := E) m Y
    have hsys' := congrArg ev.map hsys
    simp only [Functor.map_comp] at hsys'
    have hnat := ((IntegralSystemRealization.calculus C.l E Y.obj.left).reductionEvaluation
      m).hom.naturality
        (compactSupportProjectionComponent d.higher.integralExchange f c K L).hom
    dsimp only [Functor.comp_map] at hnat
    apply I.map_injective
    simp only [Functor.map_comp]
    exact evaluation_rectangle (reductionEvaluation d m Y _)
      (reductionEvaluation d m Y _) s r hnat hs hr hp hsys'
  · intro X Y f _ K L
    let := FixProjectionCompactification.Coordinates.residueUnits hl Y
    have hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj := by
      rw [← (integral_residue_tor D C.l C.different E Y.obj.left).2]
      exact L.property
    let c : Compactification f.hom.left := .ofIsProper f.hom.left
    obtain ⟨s, r, hs, hr, hp⟩ := he f c K L
    have hsys := integralProperProjectionSystemNormalization d hl o z f K L hL
    let ev := evaluation (C := C) (E := E) m Y
    let I := finiteInclusion (C := C) (E := E) m Y
    have hsys' := congrArg ev.map hsys
    simp only [Functor.map_comp] at hsys'
    have hnat := ((IntegralSystemRealization.calculus C.l E Y.obj.left).reductionEvaluation
      m).hom.naturality (properViaSupport d f K L).hom
    dsimp only [Functor.comp_map] at hnat
    have hzero : (reduction d m Y).map (properViaSupport d f K L) ≫
        (targetIso d m t f c K L).hom =
      (sourceIso d m t f c K L).hom ≫
        CompactSupportFiniteProjection.component (stage d m) f c
          ((reduction d m X).obj K) ((torReduction d m Y).obj L) := by
      apply I.map_injective
      simp only [Functor.map_comp]
      exact evaluation_rectangle (reductionEvaluation d m Y _)
        (reductionEvaluation d m Y _) s r hnat hs hr hp hsys'
    let R := reduction d m
    let S := d.higher.integral
    let F := (stage d m).finite
    let T := CompactSupportFiniteProjection.partialTensor (stage d m)
    let a := d.integralNormalization.reduction m
    let KF := (R X).obj K
    let LF := (torReduction d m Y).obj L
    let N := ((d.higher.integralTensor X).obj K).obj ((S.pull f).obj L)
    let et := tensorPullIso d m t f K L
    let ai := ((d.higher.integralTensor Y).mapIso ((S.properIdentity f).app K)).app L
    let af := ((T Y).mapIso ((F.properIdentity f).app KF)).app LF
    have hsource : (R Y).map ai.hom ≫ (properSourceIso d m t f K L).hom =
        (sourceIso d m t f c K L).hom ≫ af.hom := by
      have hc := congrArg (fun q ↦ ((T Y).map q).app LF) (a.properIdentity f K)
      simp only [Functor.map_comp, NatTrans.comp_app] at hc
      dsimp only [ai, af, properSourceIso, sourceIso, Iso.trans_hom,
        Iso.app_hom, Functor.mapIso_hom]
      simp only [Category.assoc]
      rw [reassoc_of% (hn₁ Y _ _ L ((S.properIdentity f).hom.app K)), hc]
    have htarget : (R Y).map ((S.properIdentity f).hom.app N) ≫
        (properTargetIso d m t f K L).hom =
      (targetIso d m t f c K L).hom ≫ (F.properIdentity f).hom.app _ := by
      have hc := a.properIdentity f N
      have hnf := (F.properIdentity f).hom.naturality et.hom
      dsimp only [properTargetIso, targetIso, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom]
      simp only [Category.assoc]
      rw [reassoc_of% hc, ← hnf]
    have hz : ((R Y).mapIso ai).hom ≫
        (R Y).map (compactSupportProperProjection d.higher.integralExchange f K L) ≫
        ((R Y).mapIso ((S.properIdentity f).app N)).inv ≫
        (targetIso d m t f c K L).hom =
      (sourceIso d m t f c K L).hom ≫
        CompactSupportFiniteProjection.component (stage d m) f c KF LF := by
      simpa only [R, S, ai, KF, LF, N, properViaSupport, Functor.map_comp,
        Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
        using hzero
    exact proper_rectangle ((R Y).mapIso ai)
      ((R Y).mapIso ((S.properIdentity f).app N)) af
      ((F.properIdentity f).app _) hsource htarget hz

end WeilConjectures
