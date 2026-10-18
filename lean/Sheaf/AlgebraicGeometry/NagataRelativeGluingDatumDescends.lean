/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent
import Sheaf.AlgebraicGeometry.NagataMorphismDescends

/-!
# Recovery of the raw relative gluing datum

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 359;
Stacks Project, Tag 01ZM, proof of (1), stages i₂ through i₄
(blueprint: lemma-nagata-relative-gluing-datum-descends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem chart_recovers
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i) (j : Over i)
    {U V : Scheme.{u}} (e : (baseChangeCone D c p).pt ≅ U) (s : U ⟶ c.pt)
    (hs : e.inv ≫ pullback.snd p (c.π.app i) = s)
    (hV : V = (baseChangeDiagram D p).obj j) :
    IsPullback (e.inv ≫ (baseChangeCone D c p).π.app j ≫ eqToHom hV.symm) s
      (eqToHom hV ≫ pullback.snd p (D.map j.hom)) (c.π.app j.left) := by
  subst V
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply (isPullback_baseChangeCone_π D c p j).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · rw [← hs]
    simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · rfl
  · rfl

private theorem cone_preimage
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    {j k : Over i} (a : j ⟶ k) (U : ((baseChangeDiagram D p).obj k).Opens) :
    (baseChangeCone D c p).π.app j ⁻¹ᵁ ((baseChangeDiagram D p).map a ⁻¹ᵁ U) =
      (baseChangeCone D c p).π.app k ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, (baseChangeCone D c p).w a]

private theorem transportedOpen_recovers
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    {j k : Over i} (a : j ⟶ k)
    {U : ((baseChangeDiagram D p).obj k).Opens}
    {V : ((baseChangeDiagram D p).obj j).Opens}
    {W : (baseChangeCone D c p).pt.Opens}
    (hV : V = (baseChangeDiagram D p).map a ⁻¹ᵁ U)
    (hU : (baseChangeCone D c p).π.app k ⁻¹ᵁ U = W) :
    (baseChangeCone D c p).π.app j ⁻¹ᵁ V = W := by
  rw [hV, cone_preimage]
  exact hU

private theorem selectedOpen_recovers
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {hc : IsLimit c}
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    {i : I} {Y : Scheme.{u}} {p : Y ⟶ D.obj (op i)}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    {W : (baseChangeCone D c p).pt.Opens} {hW : IsCompact W.carrier}
    {d : I → I → I} {hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b} {r : LinearOrder I}
    (Q : NagataRawOverlapOpenChoice D c hc i p W hW d hd r) :
    (baseChangeCone D c p).π.app (Over.mk (homOfLE Q.stageGE).op) ⁻¹ᵁ Q.selected = W := by
  have h := nagataQCOpenDescent_spec D c hc i p W hW Q.count Q.cover Q.affine Q.covers
    Q.basicCount Q.sectionValue Q.presentation Q.liftStage Q.liftGE Q.lift Q.lift_eq d hd r
  have h' : (fun z : Σ' s : I, Σ' hs : i ≤ s,
      ((baseChangeDiagram D p).obj (Over.mk (homOfLE hs).op)).Opens ↦
      (baseChangeCone D c p).π.app (Over.mk (homOfLE z.2.1).op) ⁻¹ᵁ z.2.2 = W)
      ⟨Q.stage, Q.stageGE, Q.selected⟩ := by
    rw [Q.selected_eq]
    exact h.2
  exact h'

private theorem transport_recovers
    {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
    {i : I} {Y Z : Scheme.{u}} {p : Y ⟶ D.obj (op i)} {q : Z ⟶ D.obj (op i)}
    {s : I} {hs : i ≤ s}
    {g : Over.mk (pullback.snd p (D.map (homOfLE hs).op)) ⟶
      Over.mk (pullback.snd q (D.map (homOfLE hs).op))}
    {t : I} {ht : i ≤ t} {hst : s ≤ t}
    (T : NagataRawMorphismTransport D i p q s hs g t ht hst)
    (phi : (baseChangeCone D c p).pt ⟶ (baseChangeCone D c q).pt)
    (hphi : phi ≫ pullback.snd q (c.π.app (op i)) =
      pullback.snd p (c.π.app (op i)))
    (hg : (baseChangeCone D c p).π.app (Over.mk (homOfLE hs).op) ≫ g.left =
      phi ≫ (baseChangeCone D c q).π.app (Over.mk (homOfLE hs).op)) :
    (baseChangeCone D c p).π.app (Over.mk (homOfLE ht).op) ≫ T.map.left =
      phi ≫ (baseChangeCone D c q).π.app (Over.mk (homOfLE ht).op) := by
  let a : Over.mk (homOfLE ht).op ⟶ Over.mk (homOfLE hs).op :=
    Over.homMk (homOfLE hst).op (Subsingleton.elim _ _)
  have h : ((baseChangeCone D c p).π.app (Over.mk (homOfLE ht).op) ≫ T.map.left) ≫
        (baseChangeDiagram D q).map a =
      (phi ≫ (baseChangeCone D c q).π.app (Over.mk (homOfLE ht).op)) ≫
        (baseChangeDiagram D q).map a := by
    rw [Category.assoc, T.map_eq, ← Category.assoc,
      (baseChangeCone D c p).w a, hg, Category.assoc, (baseChangeCone D c q).w a]
  apply pullback.hom_ext
  · have h' := congrArg (fun k ↦ k ≫ pullback.fst q (D.map (homOfLE hs).op)) h
    have hf : (baseChangeDiagram D q).map a ≫
        pullback.fst q (D.map (homOfLE hs).op) =
        pullback.fst q (D.map (homOfLE ht).op) := baseChangeDiagram_map_fst D q a
    simpa only [Category.assoc, hf] using h'
  · have hT : T.map.left ≫ pullback.snd q (D.map (homOfLE ht).op) =
        pullback.snd p (D.map (homOfLE ht).op) := T.map.w
    change ((baseChangeCone D c p).π.app (Over.mk (homOfLE ht).op) ≫ T.map.left) ≫
        pullback.snd q (D.map (homOfLE ht).op) =
      (phi ≫ (baseChangeCone D c q).π.app (Over.mk (homOfLE ht).op)) ≫
        pullback.snd q (D.map (homOfLE ht).op)
    have hp : (baseChangeCone D c p).π.app (Over.mk (homOfLE ht).op) ≫
        pullback.snd p (D.map (homOfLE ht).op) =
        pullback.snd p (c.π.app (op i)) ≫ c.π.app (op t) :=
      baseChangeCone_π_app_snd D c p (Over.mk (homOfLE ht).op)
    have hq : (baseChangeCone D c q).π.app (Over.mk (homOfLE ht).op) ≫
        pullback.snd q (D.map (homOfLE ht).op) =
        pullback.snd q (c.π.app (op i)) ≫ c.π.app (op t) :=
      baseChangeCone_π_app_snd D c q (Over.mk (homOfLE ht).op)
    rw [Category.assoc, hT, Category.assoc, hp, hq, ← Category.assoc, hphi]

/-- Every raw chart, overlap open, and overlap map recovers its named counterpart.
Source: blueprint node order 359; Stacks Project, Tag 01ZM, proof of (1), stages i₂--i₄
(blueprint: lemma-nagata-relative-gluing-datum-descends).

The first conjunct uses the fixed chart comparison and the canonical projection to the
raw chart to exhibit the named chart as its base change. The second conjunct recovers
both named overlap opens in the limit charts. Their identification with the presentation's
basic opens is `R.opens.leftOpen_eq` and `R.opens.rightOpen_eq`. The last conjunct gives
both overlap-map comparisons using the canonical projections of `baseChangeCone`;
`R.overlaps.overlapIso_canonical` identifies the limit map with the named overlap map.

Proof:
1. The base-change projection square is a pullback by the fibre-product universal
   property (`isPullback_baseChangeCone_π`). Transport this square along the fixed
   chart comparison and `rawChart_eq`. The equation `chartComparison_snd` identifies
   its other projection with the chart's structure map, giving the first conjunct.
2. Apply `nagataQCOpenDescent_spec` to each retained open choice. Its `selected_eq`
   identifies the selected output with that construction. Twice use cone naturality
   and composition of inverse images to transport recovery through the common overlap
   stage to the raw stage. This gives both equalities in the second conjunct.
3. The paired morphism choice retains the qcqs and finite-presentation instances needed
   by `nagataMorphismDescends`. Apply it to `forwardChoice` and `backwardChoice`, and use
   `forward_eq` and `backward_eq` to recover the chosen finite-stage maps.
4. For either direction, compose `map_eq` with the limit projection. Cone naturality
   and Step 3 identify the resulting maps to the earlier target model. Composing with
   its first pullback projection gives equality of the first projections at the raw
   stage. The over-base equation for the transported map and `limitOver` give equality
   of the second projections. Pullback extensionality proves the required raw-stage
   equation. No inverse or cocycle equation at the raw stage is claimed. -/
theorem nagataRelativeGluingDatum_descends
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f) :
    (∀ j : Σ a, R.base.base.chartIndex a,
      IsPullback
        ((R.charts.chartComparison j).inv ≫
          (baseChangeCone D c (R.charts.chartMap j)).π.app
            (Over.mk (homOfLE
              ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op) ≫
          eqToHom (R.raw.rawChart_eq j).symm)
        ((R.base.base.chart j.1 j.2).ι ≫ f)
        (eqToHom (R.raw.rawChart_eq j) ≫ pullback.snd (R.charts.chartMap j)
          (D.map (homOfLE
            ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op))
        (c.π.app (op R.raw.stage))) ∧
    (∀ (j k : Σ a, R.base.base.chartIndex a) (l : R.base.base.overlapIndex j k),
      ((baseChangeCone D c (R.charts.chartMap j)).π.app
        (Over.mk (homOfLE
          ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op) ⁻¹ᵁ
            R.raw.rawLeftOpen j k l = R.opens.leftOpen j k l) ∧
      ((baseChangeCone D c (R.charts.chartMap k)).π.app
        (Over.mk (homOfLE
          ((R.stages.chart_le_overlap k).trans R.raw.overlap_le_raw)).op) ⁻¹ᵁ
            R.raw.rawRightOpen j k l = R.opens.rightOpen j k l)) ∧
    (∀ (j k : Σ a, R.base.base.chartIndex a) (l : R.base.base.overlapIndex j k),
      ((baseChangeCone D c (R.schemes.leftMap j k l)).π.app
        (Over.mk (homOfLE R.raw.overlap_le_raw).op) ≫
          (R.raw.forwardRaw j k l).map.left =
        (R.overlaps.overlapIso j k l).hom ≫
          (baseChangeCone D c (R.schemes.rightMap j k l)).π.app
            (Over.mk (homOfLE R.raw.overlap_le_raw).op)) ∧
      ((baseChangeCone D c (R.schemes.rightMap j k l)).π.app
        (Over.mk (homOfLE R.raw.overlap_le_raw).op) ≫
          (R.raw.backwardRaw j k l).map.left =
        (R.overlaps.overlapIso j k l).inv ≫
          (baseChangeCone D c (R.schemes.leftMap j k l)).π.app
            (Over.mk (homOfLE R.raw.overlap_le_raw).op))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact chart_recovers D c (R.charts.chartMap j) _ (R.charts.chartComparison j) _
      (R.charts.chartComparison_snd j) (R.raw.rawChart_eq j)
  · intro j k l
    constructor
    · exact transportedOpen_recovers D c _ _ (R.raw.rawLeftOpen_eq j k l)
        (transportedOpen_recovers D c _ _ (R.stages.leftAtOverlap_eq j k l)
          (selectedOpen_recovers (R.opens.openChoice j k l)))
    · exact transportedOpen_recovers D c _ _ (R.raw.rawRightOpen_eq j k l)
        (transportedOpen_recovers D c _ _ (R.stages.rightAtOverlap_eq j k l)
          (selectedOpen_recovers (R.opens.rightOpenChoice j k l)))
  · intro j k l
    let M := R.morphisms.choice j k l
    have := M.baseCompact
    have := M.baseQS
    have := M.leftCompact
    have := M.leftQS
    have := M.rightCompact
    have := M.rightQS
    have := M.leftLFP
    have := M.leftQC
    have := M.leftMapQS
    have := M.rightLFP
    have := M.rightQC
    have := M.rightMapQS
    constructor
    · have h := nagataMorphismDescends M.forwardChoice
      rw [← M.forward_eq] at h
      exact transport_recovers (R.raw.forwardRaw j k l) _ M.forwardChoice.limitOver h
    · have h := nagataMorphismDescends M.backwardChoice
      rw [← M.backward_eq] at h
      exact transport_recovers (R.raw.backwardRaw j k l) _ M.backwardChoice.limitOver h

end AlgebraicGeometry
