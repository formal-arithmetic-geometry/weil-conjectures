/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage
import Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually
import Sheaf.Order.DirectedFiniteUpperBound

/-!
# Eventual equality of descended morphisms

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
sk-prop-nagata-sketch-approximation/lemma-nagata-morphism-eq-eventually.md,
node order 356 (blueprint: lemma-nagata-morphism-eq-eventually).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (b : Γ(Z, ⊤)) : (f ≫ g).appTop b = f.appTop (g.appTop b) := by
  simp

private theorem hom_eq_of_generators {Z V T : Scheme.{u}} [IsAffine V]
    (f g : Z ⟶ V) (t : V ⟶ T) (G : Finset Γ(V, ⊤))
    (hG : Subring.closure (Set.range t.appTop ∪ (G : Set Γ(V, ⊤))) = ⊤)
    (hbase : f ≫ t = g ≫ t)
    (heq : ∀ b ∈ G, f.appTop b = g.appTop b) : f = g := by
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.eq_of_eqOn_set_dense hG
  intro b hb
  rcases hb with ⟨a, rfl⟩ | hb
  · have h := congrArg (fun k : Z ⟶ T ↦ k.appTop a) hbase
    simpa [Scheme.Hom.comp_appTop] using h
  · exact heq b hb

/-- For every stage above the selected equality stage, the two base-changed
morphisms are equal.
Source: blueprint node order 356; Stacks Project, Tag 01ZM (3), proof
(blueprint: lemma-nagata-morphism-eq-eventually).

Proof:
1. The choices in `def-nagata-morphism-equality-stage` give the compact inverse-image
   opens W1 and W2, their selected equality stages lambdaJK, affine covers U of their
   intersections, and coefficient equality stages mu for all target generators.
   By `lemma-nagata-directed-finite-upper-bound`, the selected finite upper bound
   dominates i₀, every lambdaJK and every mu.
2. At any lambda above that bound, `lemma-nagata-qc-open-eq-eventually`, applied
   with X₀ as its base-changed scheme, makes the two transported opens equal.
   Thus the inverse images of the U cover each transported W1. Since the target
   charts cover Y₀, the W1 cover X₀, and these U together cover X_lambda.
3. Transport each coefficient equality from its mu to lambda by the transition
   map on sections. The two maps from each U to its affine target chart agree
   on all algebra generators and on the base ring, since both lie over the same
   base chart. They are therefore equal as algebra maps, hence as scheme maps.
   The two base-changed maps on U have equal projections to Y₀ and S_lambda;
   the fibre-product universal property makes them equal. Open-cover
   extensionality then gives equality on X_lambda. -/
theorem nagataMorphismEqEventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {hc : IsLimit c}
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    {p : X₀ ⟶ D.obj (op i₀)} {q : Y₀ ⟶ D.obj (op i₀)}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {phi psi : X₀ ⟶ Y₀} {hphi : phi ≫ q = p} {hpsi : psi ≫ q = p}
    {d : I → I → I} {r : LinearOrder I}
    (data : NagataMorphismEqualityStageData D c hc i₀ p q phi psi hphi hpsi d r)
    : ∀ (lambda : I) (hlambda : i₀ ≤ lambda),
      nagataMorphismEqualityStage data ≤ lambda →
      ((Over.pullback (D.map (homOfLE hlambda).op)).map
          (Over.homMk (U := Over.mk p) (V := Over.mk q) phi hphi)).left =
        ((Over.pullback (D.map (homOfLE hlambda).op)).map
          (Over.homMk (U := Over.mk p) (V := Over.mk q) psi hpsi)).left := by
  classical
  let := data.finiteJ
  let : ∀ j, Fintype (data.K j) := data.finiteK
  let : ∀ j k, Fintype (data.L j k) := data.finiteL
  have hJK (j : data.J) (k : data.K j) :
      data.lambdaJK j k ≤ nagataMorphismEqualityStage data := by
    apply le_directedFiniteUpperBound i₀ d data.boundData r
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, k, Or.inl rfl⟩
  have hmu (j : data.J) (k : data.K j) (l : data.L j k) (b : data.G j k) :
      (data.mu j k l b).left.unop ≤ nagataMorphismEqualityStage data := by
    apply le_directedFiniteUpperBound i₀ d data.boundData r
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, k, Or.inr ⟨l, Finset.mem_image.mpr ⟨b, by simp, rfl⟩⟩⟩
  intro lambda hlambda hstage
  let B := baseChangeDiagram D p
  let idx : Over (op i₀) := Over.mk (homOfLE hlambda).op
  let idxJK (j : data.J) (k : data.K j) : Over (op i₀) :=
    Over.mk (homOfLE (data.lambdaGE j k)).op
  let transition (j : data.J) (k : data.K j) : B.obj idx ⟶ B.obj (idxJK j k) :=
    B.map (Over.homMk (homOfLE ((hJK j k).trans hstage)).op)
  have transition_fst (j : data.J) (k : data.K j) :
      transition j k ≫ pullback.fst p (D.map (homOfLE (data.lambdaGE j k)).op) =
        pullback.fst p (D.map (homOfLE hlambda).op) := by
    exact baseChangeDiagram_map_fst D p _
  have transition_snd (j : data.J) (k : data.K j) :
      transition j k ≫ pullback.snd p (D.map (homOfLE (data.lambdaGE j k)).op) =
        pullback.snd p (D.map (homOfLE hlambda).op) ≫
          D.map (homOfLE ((hJK j k).trans hstage)).op := by
    exact baseChangeDiagram_map_snd D p _
  let W (j : data.J) (k : data.K j) (l : data.L j k) : (B.obj idx).Opens :=
    transition j k ⁻¹ᵁ data.U j k l
  have hW (j : data.J) (k : data.K j) :
      ⨆ l, W j k l =
        pullback.fst p (D.map (homOfLE hlambda).op) ⁻¹ᵁ (phi ⁻¹ᵁ data.V j k) := by
    have hopen := nagataQCOpenEqEventually D c hc i₀ p
      (phi ⁻¹ᵁ data.V j k) (psi ⁻¹ᵁ data.V j k)
      (data.compactPhi j k) (data.compactPsi j k) (data.equalOpens j k)
      d data.boundData r lambda hlambda
      (by rw [← data.selectedLambda j k]; exact (hJK j k).trans hstage)
    simp only [W, ← Scheme.Hom.preimage_iSup, data.coverU]
    have hpre (O : X₀.Opens) :
        transition j k ⁻¹ᵁ
            (pullback.fst p (D.map (homOfLE (data.lambdaGE j k)).op) ⁻¹ᵁ O) =
          pullback.fst p (D.map (homOfLE hlambda).op) ⁻¹ᵁ O := by
      rw [← Scheme.Hom.comp_preimage, transition_fst]
    rw [Scheme.Hom.preimage_inf, hpre, hpre, hopen, inf_idem]
  have hcover : (⨆ x : Σ j, Σ k : data.K j, data.L j k,
      W x.1 x.2.1 x.2.2) = ⊤ := by
    simp only [iSup_sigma, hW, ← Scheme.Hom.preimage_iSup, data.coverV,
      Scheme.Hom.preimage_top]
  have hlocal (j : data.J) (k : data.K j) (l : data.L j k) :
      (W j k l).ι ≫ pullback.fst p (D.map (homOfLE hlambda).op) ≫ phi =
        (W j k l).ι ≫ pullback.fst p (D.map (homOfLE hlambda).op) ≫ psi := by
    let a : (W j k l).toScheme ⟶ (data.U j k l).toScheme :=
      (transition j k).resLE (data.U j k l) (W j k l) le_rfl
    have ha : a ≫ (data.U j k l).ι = (W j k l).ι ≫ transition j k :=
      Scheme.Hom.resLE_comp_ι _ _
    have hbase : data.phiU j k l ≫ data.chartMap j k =
        data.psiU j k l ≫ data.chartMap j k := by
      apply (cancel_mono (data.T j).ι).mp
      calc
        (data.phiU j k l ≫ data.chartMap j k) ≫ (data.T j).ι =
            (data.phiU j k l ≫ (data.V j k).ι) ≫ q := by
          rw [Category.assoc, data.chartOver, ← Category.assoc]
        _ = (data.U j k l).ι ≫
            pullback.fst p (D.map (homOfLE (data.lambdaGE j k)).op) ≫ p := by
          rw [data.overPhi]; simp only [Category.assoc, hphi]
        _ = (data.psiU j k l ≫ (data.V j k).ι) ≫ q := by
          rw [data.overPsi]; simp only [Category.assoc, hpsi]
        _ = (data.psiU j k l ≫ data.chartMap j k) ≫ (data.T j).ι := by
          simp only [Category.assoc, data.chartOver]
    have hcoeff (b : data.G j k) :
        (a ≫ data.phiU j k l).appTop b.val =
          (a ≫ data.psiU j k l).appTop b.val := by
      let mu := data.mu j k l b
      have hmulambda : mu.left.unop ≤ lambda := (hmu j k l b).trans hstage
      let v : (W j k l).toScheme ⟶ D.obj mu.left :=
        (W j k l).ι ≫ pullback.snd p (D.map (homOfLE hlambda).op) ≫
          D.map (homOfLE hmulambda).op
      have hv : a ≫ ((data.U j k l).ι ≫
          pullback.snd p (D.map (homOfLE (data.lambdaGE j k)).op)) =
            v ≫ D.map mu.hom := by
        rw [← Category.assoc, ha, Category.assoc, transition_snd]
        dsimp only [v]
        simp only [Category.assoc, ← D.map_comp]
        congr 3
      let lift : (W j k l).toScheme ⟶
          pullback ((data.U j k l).ι ≫
            pullback.snd p (D.map (homOfLE (data.lambdaGE j k)).op))
            (D.map mu.hom) := pullback.lift a v hv
      have heq := congrArg (fun z ↦ lift.appTop z) (data.coefficientEquality j k l b)
      have hlift : lift ≫ pullback.fst ((data.U j k l).ι ≫
          pullback.snd p (D.map (homOfLE (data.lambdaGE j k)).op))
            (D.map mu.hom) = a := pullback.lift_fst _ _ _
      have hf (z : Γ((data.U j k l).toScheme, ⊤)) :
          lift.appTop ((pullback.fst ((data.U j k l).ι ≫
            pullback.snd p (D.map (homOfLE (data.lambdaGE j k)).op))
              (D.map mu.hom)).appTop z) = a.appTop z := by
        simpa only [comp_appTop_apply] using congrArg (fun f ↦ f.appTop z) hlift
      simpa only [comp_appTop_apply] using
        (hf ((data.phiU j k l).appTop b.val)).symm.trans
          (heq.trans (hf ((data.psiU j k l).appTop b.val)))
    let : IsAffine (data.V j k).toScheme := data.affineV j k
    have heq : a ≫ data.phiU j k l = a ≫ data.psiU j k l :=
      hom_eq_of_generators _ _ (data.chartMap j k) (data.G j k)
        (data.generatorsGenerate j k)
        (by simpa only [Category.assoc] using congrArg (a ≫ ·) hbase)
        (fun b hb ↦ hcoeff ⟨b, hb⟩)
    have heq' := congrArg (· ≫ (data.V j k).ι) heq
    have hproj : a ≫ (data.U j k l).ι ≫
        pullback.fst p (D.map (homOfLE (data.lambdaGE j k)).op) =
          (W j k l).ι ≫ pullback.fst p (D.map (homOfLE hlambda).op) := by
      rw [← Category.assoc, ha, Category.assoc, transition_fst]
    have heq'' : (a ≫ (data.U j k l).ι ≫
        pullback.fst p (D.map (homOfLE (data.lambdaGE j k)).op)) ≫ phi =
          (a ≫ (data.U j k l).ι ≫
            pullback.fst p (D.map (homOfLE (data.lambdaGE j k)).op)) ≫ psi := by
      simpa only [Category.assoc, data.overPhi, data.overPsi] using heq'
    rw [hproj] at heq''
    exact heq''
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    exact Scheme.Opens.hom_ext_of_iSup_eq_top _ hcover _ _
      (fun x ↦ hlocal x.1 x.2.1 x.2.2)
  · simp only [Over.pullback_map_left, pullback.lift_snd]

end AlgebraicGeometry
