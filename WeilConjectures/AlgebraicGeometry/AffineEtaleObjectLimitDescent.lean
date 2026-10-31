/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import WeilConjectures.SixFunctors.QcqsLfpObjectLimitModel
import WeilConjectures.AlgebraicGeometry.EtaleAffineChartDescent
import Mathlib.Data.Finset.Order
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Affine etale objects descend along affine-transition limits

Source: Stacks Project, etale-cohomology.tex, Tag 0EYL,
lemma-colimit-affine-sites, general-case essential surjectivity.
(blueprint: lem-sf-affine-etale-object-limit-descent)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite-chart argument for eventual etaleness only needs a compact source.
Source: Stacks Project Tag 0EYL, general-case proof; Tag 07RP on each affine chart.
The proof adapts `Etale.exists_stage_of_inverseLimit`, retaining only the hypotheses used.
(blueprint: lem-sf-affine-etale-object-limit-descent) -/
private theorem exists_etale_stage_of_compact_source
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : Etale (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (_ : i₀ ≤ i), ∀ (j : I) (_ : i ≤ j) (hj : i₀ ≤ j),
      Etale (((Over.pullback (D.map (homOfLE hj).op)).map f₀).left) := by
  classical
  have local_chart (x : X₀.left) :
      ∃ (U : X₀.left.Opens), x ∈ U ∧
        ∃ (i : I) (_ : i₀ ≤ i), ∀ (j : I) (_ : i ≤ j) (hj : i₀ ≤ j),
          Etale (((pullback.fst X₀.hom (D.map (homOfLE hj).op)) ⁻¹ᵁ U).ι ≫
            ((Over.pullback (D.map (homOfLE hj).op)).map f₀).left) := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := D.obj (op i₀)) (x := Y₀.hom (f₀.left x)) (U := ⊤) (by simp)
    obtain ⟨V, hV, hxV, eV⟩ := exists_isAffineOpen_mem_and_subset
      (X := Y₀.left) (x := f₀.left x) (U := Y₀.hom ⁻¹ᵁ W) hxW
    obtain ⟨U, hU, hxU, eU⟩ := exists_isAffineOpen_mem_and_subset
      (X := X₀.left) (x := x) (U := f₀.left ⁻¹ᵁ V) hxV
    refine ⟨U, hxU, Etale.exists_stage_on_affine_chart D c hc i₀ X₀ Y₀ f₀
      W hW V hV eV U hU eU ?_⟩
    have := hf
    infer_instance
  choose U hxU k hk hstage using local_chart
  have hcover : (Set.univ : Set X₀.left) ⊆ ⋃ x, (U x : Set X₀.left) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X₀.left)) (fun x ↦ (U x).isOpen) hcover
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨i, hi⟩ := (insert i₀ (s.image k)).exists_le
  have hi₀ : i₀ ≤ i := hi i₀ (Finset.mem_insert_self _ _)
  refine ⟨i, hi₀, ?_⟩
  intro j hij hj₀
  let q := D.map (homOfLE hj₀).op
  have hU : (⨆ x : s, U x) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun x : s ↦ (pullback.fst X₀.hom q) ⁻¹ᵁ U x)
    ((pullback.fst X₀.hom q).iSup_preimage_eq_top hU)
  intro x
  exact hstage x j ((hi (k x) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨x, x.property, rfl⟩))).trans hij) hj₀

/-- An affine etale object over an affine-transition limit descends to a stage.
There is no quasi-compactness or quasi-separatedness assumption on the bases.

Source: Stacks Project, etale-cohomology.tex, Tag 0EYL,
lemma-colimit-affine-sites, general-case essential-surjectivity proof.
(blueprint: lem-sf-affine-etale-object-limit-descent)

Proof (the node's five steps):
1. The affine source W is qcqs (lem-weil-pbc-affine-scheme-qcqs), and its
   etale structure map is locally of finite presentation (def-weil-etale-morphism).
   Apply lem-sf-qcqs-lfp-object-limit-model, the object part of Tag 0EY1, to obtain
   a qcqs locally finitely presented model U at a stage i₀.
2. Base change U over the category Over (op i₀). By lem-weil-pbc-scheme-over-limit
   its limit is W. The first projections are affine by affine-morphism permanence,
   so the source schemes are qcqs by lem-weil-pbc-qcqs-morphism-permanence.
   Apply lem-weil-pbc-limit-affine-stage (Tag 01Z6) to obtain an affine stage i₁.
3. Independently choose affine source and target opens around each point of U at i₀,
   with the target open contained in an affine base open, using
   lem-weil-pbc-affine-opens-basis. Extract a finite source subcover by
   def-weil-pbc-quasi-compact-scheme; an empty source allows the empty cover.
4. Apply lem-weil-pbc-etale-affine-chart-descent to each triple, with Y₀ the base
   over itself. The limit map is etale by the model isomorphism and the canonical
   isomorphism Y₀ × S ≅ S. Its restrictions are etale by
   lem-weil-pbc-etale-composition-cancellation. Choose a common threshold for the
   finitely many charts. Their inverse images cover every later source, so
   lem-weil-pbc-etale-local-on-source makes its structure map etale.
5. Choose a stage above both i₁ and this threshold. Its source is affine because
   the transition to i₁ is affine. The base-change cone's pullback square gives the
   required isomorphism over the limit (def-pc-fibre-product), with its projection
   equation supplied by the pullback isomorphism's second projection equation.
-/
theorem Scheme.exists_affine_etale_model_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
    (W : Scheme.{u}) [IsAffine W] (f : W ⟶ c.pt) [Etale f] :
    ∃ (i : I) (Wᵢ : Scheme.{u}) (fᵢ : Wᵢ ⟶ D.obj (op i)),
      IsAffine Wᵢ ∧ Etale fᵢ ∧
        ∃ e : W ≅ pullback fᵢ (c.π.app (op i)),
          e.hom ≫ pullback.snd fᵢ (c.π.app (op i)) = f := by
  classical
  obtain ⟨i₀, X, p, hXc, hXs, hp, e, he⟩ :=
    exists_qcqs_lfp_object_limit_model D c hc W f
  have : CompactSpace X := hXc
  have : QuasiSeparatedSpace X := hXs
  have : LocallyOfFinitePresentation p := hp
  have het : Etale (pullback.snd p (c.π.app (op i₀))) := by
    have : Etale (e.inv ≫ f) := inferInstance
    simpa only [← he, Iso.inv_hom_id_assoc] using this
  have : IsAffine (baseChangeCone D c p).pt := IsAffine.of_isIso e.inv
  have (j : Over (op i₀)) : CompactSpace ((baseChangeDiagram D p).obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map j.hom))
  have (j : Over (op i₀)) : QuasiSeparatedSpace ((baseChangeDiagram D p).obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (D.map j.hom))
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit (baseChangeDiagram D p)
    (baseChangeCone D c p) (isLimitBaseChangeCone D c p hc)
  let X₀ : Over (D.obj (op i₀)) := Over.mk p
  let Y₀ : Over (D.obj (op i₀)) := Over.mk (𝟙 _)
  let g : X₀ ⟶ Y₀ := Over.homMk p (by change p ≫ 𝟙 _ = p; simp)
  have : CompactSpace X₀.left := hXc
  have : LocallyOfFinitePresentation g.left := hp
  have hg : Etale (((Over.pullback (c.π.app (op i₀))).map g).left) := by
    have : Etale (((Over.pullback (c.π.app (op i₀))).map g).left ≫
        pullback.snd (𝟙 _) (c.π.app (op i₀))) := by
      rw [show ((Over.pullback (c.π.app (op i₀))).map g).left ≫
          pullback.snd (𝟙 _) (c.π.app (op i₀)) =
          pullback.snd p (c.π.app (op i₀)) from
        Over.w ((Over.pullback (c.π.app (op i₀))).map g)]
      exact het
    exact Etale.of_comp _ (pullback.snd (𝟙 _) (c.π.app (op i₀)))
  obtain ⟨k, hk, hkg⟩ := exists_etale_stage_of_compact_source D c hc i₀ X₀ Y₀ g hg
  obtain ⟨l, hkl, hjl⟩ := exists_ge_ge k j.left.unop
  have hl : i₀ ≤ l := hk.trans hkl
  let j' : Over (op i₀) := Over.mk (homOfLE hl).op
  let a : j' ⟶ j := Over.homMk (homOfLE hjl).op
  have : IsAffine ((baseChangeDiagram D p).obj j) := hj
  have : IsAffine ((baseChangeDiagram D p).obj j') :=
    isAffine_of_isAffineHom ((baseChangeDiagram D p).map a)
  have hgl := hkg l hkl hl
  have hel : Etale (pullback.snd p (D.map (homOfLE hl).op)) := by
    have : Etale (((Over.pullback (D.map (homOfLE hl).op)).map g).left) := hgl
    have hcomp : Etale
        (((Over.pullback (D.map (homOfLE hl).op)).map g).left ≫
          pullback.snd (𝟙 _) (D.map (homOfLE hl).op)) := inferInstance
    rw [show ((Over.pullback (D.map (homOfLE hl).op)).map g).left ≫
        pullback.snd (𝟙 _) (D.map (homOfLE hl).op) =
        pullback.snd p (D.map (homOfLE hl).op) from
      Over.w ((Over.pullback (D.map (homOfLE hl).op)).map g)] at hcomp
    exact hcomp
  refine ⟨l, (baseChangeDiagram D p).obj j', pullback.snd p (D.map (homOfLE hl).op),
    inferInstance, hel, e ≪≫ (isPullback_baseChangeCone_π D c p j').isoPullback, ?_⟩
  change (e.hom ≫ (isPullback_baseChangeCone_π D c p j').isoPullback.hom) ≫
    pullback.snd ((baseChangeDiagramπ D p).app j') (c.π.app j'.left) = f
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]
  exact he

end AlgebraicGeometry
