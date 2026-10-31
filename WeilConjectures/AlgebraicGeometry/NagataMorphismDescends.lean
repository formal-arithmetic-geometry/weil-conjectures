/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NagataMorphismDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The selected finite-stage morphism recovers the original morphism

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 354
(blueprint: lemma-nagata-morphism-descends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Equality on base sections and presentation generators determines a map to an affine
scheme, by surjectivity of polynomial evaluation and `ext_of_isAffine`. -/
private theorem affine_ext_generators
    {Z V T : Scheme.{u}} [IsAffine V] (t : V ⟶ T)
    {n m : ℕ}
    (P : @Algebra.Presentation Γ(T, ⊤) Γ(V, ⊤) (Fin n) (Fin m)
      _ _ t.appTop.hom.toAlgebra)
    (f g : Z ⟶ V) (hbase : f ≫ t = g ≫ t) :
    let _ : Algebra Γ(T, ⊤) Γ(V, ⊤) := t.appTop.hom.toAlgebra
    (∀ z, f.appTop (P.toGenerators.val z) = g.appTop (P.toGenerators.val z)) → f = g := by
  dsimp only
  intro hgen
  let _ : Algebra Γ(T, ⊤) Γ(V, ⊤) := t.appTop.hom.toAlgebra
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.cancel_right P.toGenerators.aeval_val_surjective |>.mp
  apply MvPolynomial.ringHom_ext
  · intro a
    have h := congrArg (fun e => e.appTop a) hbase
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.coe_coe,
      MvPolynomial.aeval_C, RingHom.algebraMap_toAlgebra] using h
  · intro z
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.aeval_X] using hgen z

/-- The glued morphism at the prescribed finite upper bound has base change `phi`.
Source: blueprint node order 354 (blueprint: lemma-nagata-morphism-descends).
The equation uses the canonical projections of `baseChangeCone`. Since `phi` and the
selected morphism are over their respective bases, the fibre-product universal property
identifies this equation with equality of the base-changed morphism and `phi`.

Proof:
1. Cone naturality and `chart_eq` identify the inverse image of each chart at
   any later stage with `limitChart`. Pull back `charts_cover` to obtain an open
   cover of the limit source by these charts.
2. Restrict the projection to the final-stage chart and compose with `toCoefficient`.
   The comparison equations identify its further composite to the generator stage
   with `limitToGenerator`. Thus `localGenerators`, `coefficientLift_eq` and
   `generatorLift_eq` give equality with `limitMap` on every presentation generator.
   Both maps have the same composite to the affine base chart, by `localOver`,
   `limitMap_eq`, `targetOver`, and `limitOver`. Polynomial evaluation is surjective
   for the given presentation, so the section maps agree, and `ext_of_isAffine`
   identifies the morphisms to the affine target chart.
3. The restriction of the glued morphism is `mapAt`, by `Scheme.Cover.ι_glueMorphisms`.
   Its first pullback projection agrees with phi by Step 2 and `mapAt_fst`; its
   second agrees by `mapAt_snd` and `limitOver`. Pullback extensionality gives equality
   on each limit chart. Open-cover extensionality gives the displayed equation. -/
theorem nagataMorphismDescends
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {hc : IsLimit c}
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    {p : X₀ ⟶ D.obj (op i₀)} {q : Y₀ ⟶ D.obj (op i₀)}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {phi : (baseChangeCone D c p).pt ⟶ (baseChangeCone D c q).pt}
    {d : I → I → I} {hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j} {r : LinearOrder I}
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) :
    (baseChangeCone D c p).π.app
        (Over.mk (homOfLE (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.1).op) ≫
      (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.2.left =
    phi ≫ (baseChangeCone D c q).π.app
        (Over.mk (homOfLE (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.1).op) := by
  classical
  let π (s : I) (hs : i₀ ≤ s) :=
    (baseChangeCone D c p).π.app (Over.mk (homOfLE hs).op)
  have hchart (j : Fin data.J) (k : Fin (data.K j)) (l : Fin (data.L j k))
      (s : I) (hs : data.openStage j k ≤ s) :
      π s ((data.openGE j k).trans hs) ⁻¹ᵁ data.chart j k l s hs =
        data.limitChart j k l := by
    rw [data.chart_eq, data.limitChart_eq]
    let t : Over (op i₀) := Over.mk (homOfLE ((data.openGE j k).trans hs)).op
    let o : Over (op i₀) := Over.mk (homOfLE (data.openGE j k)).op
    let f : t ⟶ o := Over.homMk (homOfLE hs).op (Subsingleton.elim _ _)
    exact congrArg (fun e => e ⁻¹ᵁ data.U j k l) ((baseChangeCone D c p).w f)
  let U (x : Σ j, Σ k : Fin (data.K j), Fin (data.L j k)) :
      ((baseChangeDiagram D p).obj
        (Over.mk (homOfLE data.base_le_stage).op)).Opens :=
    data.chart x.1 x.2.1 x.2.2 data.stage
      (((data.generatorGE x.1 x.2.1 x.2.2).trans
        (data.coefficientGE x.1 x.2.1 x.2.2)).trans
        (data.coefficient_le_stage x.1 x.2.1 x.2.2))
  have hU : iSup U = ⊤ := by
    simpa only [U, iSup_sigma] using data.charts_cover
  let finalCover := Scheme.openCoverOfIsOpenCover _ U hU
  have hlim : (⨆ j, ⨆ k, ⨆ l, data.limitChart j k l) = ⊤ := by
    have h := (π data.stage data.base_le_stage).iSup_preimage_eq_top hU
    simpa only [U, Scheme.Hom.preimage_iSup, iSup_sigma, hchart] using h
  let cover := Scheme.openCoverOfIsOpenCover _
    (fun x : Σ j, Σ k : Fin (data.K j), Fin (data.L j k) =>
      data.limitChart x.1 x.2.1 x.2.2)
    (by simpa only [TopologicalSpace.IsOpenCover, iSup_sigma] using hlim)
  apply cover.hom_ext
  rintro ⟨j, k, l⟩
  change (data.limitChart j k l).ι ≫ _ = (data.limitChart j k l).ι ≫ _
  let a := (π data.stage data.base_le_stage).resLE (U ⟨j, k, l⟩)
    (data.limitChart j k l) (hchart j k l _ _).ge
  have ha : a ≫ (U ⟨j, k, l⟩).ι =
      (data.limitChart j k l).ι ≫ π data.stage data.base_le_stage :=
    Scheme.Hom.resLE_comp_ι _ _
  have hglue : (U ⟨j, k, l⟩).ι ≫
      (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.2.left =
      data.mapAt j k l data.stage (data.coefficient_le_stage j k l) := by
    exact finalCover.ι_glueMorphisms
      (Y := (baseChangeDiagram D q).obj (Over.mk (homOfLE data.base_le_stage).op))
      (fun x => data.mapAt x.1 x.2.1 x.2.2 data.stage
        (data.coefficient_le_stage x.1 x.2.1 x.2.2)) data.charts_agree ⟨j, k, l⟩
  rw [← Category.assoc, ← ha, Category.assoc, hglue]
  change a ≫ data.mapAt j k l data.stage (data.coefficient_le_stage j k l) =
    (data.limitChart j k l).ι ≫ phi ≫
      (baseChangeCone D c q).π.app (Over.mk (homOfLE data.base_le_stage).op)
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [data.mapAt_fst j k l data.stage (data.coefficient_le_stage j k l),
      baseChangeCone_π_app_fst D c q (Over.mk (homOfLE data.base_le_stage).op)]
    let b := a ≫ data.toCoefficient j k l data.stage (data.coefficient_le_stage j k l)
    have hb : b ≫ (data.chart j k l (data.coefficientStage j k l)
        ((data.generatorGE j k l).trans (data.coefficientGE j k l))).ι =
        (data.limitChart j k l).ι ≫ π (data.coefficientStage j k l)
          ((data.openGE j k).trans
            ((data.generatorGE j k l).trans (data.coefficientGE j k l))) := by
      dsimp only [b]
      rw [Category.assoc, data.toCoefficient_eq, ← Category.assoc a, ha, Category.assoc]
      let t : Over (op i₀) := Over.mk (homOfLE data.base_le_stage).op
      let o : Over (op i₀) := Over.mk (homOfLE ((data.openGE j k).trans
        ((data.generatorGE j k l).trans (data.coefficientGE j k l)))).op
      let f : t ⟶ o := Over.homMk
        (homOfLE (data.coefficient_le_stage j k l)).op (Subsingleton.elim _ _)
      exact congrArg ((data.limitChart j k l).ι ≫ ·) ((baseChangeCone D c p).w f)
    have hbgen : b ≫ data.coefficientTransition j k l =
        data.limitToGenerator j k l := by
      apply (cancel_mono (data.chart j k l (data.generatorStage j k l)
        (data.generatorGE j k l)).ι).mp
      rw [Category.assoc, data.coefficientTransition_eq, ← Category.assoc b, hb,
        Category.assoc, data.limitToGenerator_eq]
      let t : Over (op i₀) := Over.mk (homOfLE ((data.openGE j k).trans
        ((data.generatorGE j k l).trans (data.coefficientGE j k l)))).op
      let o : Over (op i₀) := Over.mk
        (homOfLE ((data.openGE j k).trans (data.generatorGE j k l))).op
      let f : t ⟶ o := Over.homMk
        (homOfLE (data.coefficientGE j k l)).op (Subsingleton.elim _ _)
      exact congrArg ((data.limitChart j k l).ι ≫ ·) ((baseChangeCone D c p).w f)
    have hbase : (b ≫ data.localMap j k l) ≫ data.targetToBase j k =
        data.limitMap j k l ≫ data.targetToBase j k := by
      apply (cancel_mono (data.T j).ι).mp
      simp only [Category.assoc, data.targetOver]
      rw [data.localOver, ← Category.assoc b, hb]
      dsimp only [π]
      simp only [Category.assoc]
      erw [baseChangeCone_π_app_fst_assoc D c p
        (Over.mk (homOfLE ((data.openGE j k).trans
          ((data.generatorGE j k l).trans (data.coefficientGE j k l)))).op)]
      rw [← Category.assoc (data.limitMap j k l), data.limitMap_eq]
      simp only [Category.assoc]
      rw [pullback.condition, ← data.limitOver, Category.assoc,
        ← pullback.condition]
    have : IsAffine (data.V j k).toScheme := data.affineV j k
    have hlocal : b ≫ data.localMap j k l = data.limitMap j k l := by
      apply affine_ext_generators (data.targetToBase j k) (data.presentation j k)
        _ _ hbase
      intro z
      have hval := congrFun (data.generators_eq j k) z
      rw [← hval, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        data.localGenerators, data.coefficientLift_eq]
      have h := congrArg (fun e => e.appTop (data.generatorLift j k l z)) hbgen
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        data.generatorLift_eq] using h
    change a ≫ data.toCoefficient j k l data.stage
      (data.coefficient_le_stage j k l) ≫ data.localMap j k l ≫ (data.V j k).ι = _
    rw [← Category.assoc a, ← Category.assoc, hlocal, data.limitMap_eq]
  · simp only [Category.assoc]
    erw [data.mapAt_snd j k l data.stage (data.coefficient_le_stage j k l)]
    rw [← Category.assoc a, ha, Category.assoc]
    dsimp only [π]
    erw [baseChangeCone_π_app_snd D c p (Over.mk (homOfLE data.base_le_stage).op),
      baseChangeCone_π_app_snd D c q (Over.mk (homOfLE data.base_le_stage).op)]
    rw [← Category.assoc phi, data.limitOver]

end AlgebraicGeometry
