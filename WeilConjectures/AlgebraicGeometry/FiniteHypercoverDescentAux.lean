/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CofilteredLimitOverDescent
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Etale

/-!
# Auxiliary results for the descent of finite split étale hypercovers

* finite coproducts of quasi-compact quasi-separated schemes are quasi-compact and
  quasi-separated;
* the terms of a truncated finite split étale hypercover over a qcqs scheme are qcqs étale;
* transport of descended morphisms along further transition maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/-- A finite disjoint union of quasi-separated spaces is quasi-separated. -/
lemma quasiSeparatedSpace_sigma {ι : Type*} [Finite ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (Σ i, X i) := by
  refine ⟨fun U V hUo hUc hVo hVc ↦ ?_⟩
  have hU : ∀ i, IsCompact (Sigma.mk i ⁻¹' U) := fun i ↦
    Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc
  have hV : ∀ i, IsCompact (Sigma.mk i ⁻¹' V) := fun i ↦
    Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hVc
  have : U ∩ V = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' U ∩ Sigma.mk i ⁻¹' V) := by
    ext ⟨i, x⟩
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨hx, hx'⟩
      exact ⟨i, x, ⟨hx, hx'⟩, rfl⟩
    · rintro ⟨j, y, ⟨hy, hy'⟩, h⟩
      rw [← h]
      exact ⟨hy, hy'⟩
  rw [this]
  exact isCompact_iUnion fun i ↦ (QuasiSeparatedSpace.inter_isCompact _ _
    (hUo.preimage continuous_sigmaMk) (hU i) (hVo.preimage continuous_sigmaMk) (hV i)).image
    continuous_sigmaMk

namespace AlgebraicGeometry

/-- The apex of a finite coproduct of quasi-compact quasi-separated schemes is quasi-compact and
quasi-separated. -/
lemma Scheme.compactSpace_quasiSeparatedSpace_of_isColimit {ι : Type*} [Finite ι]
    {Y : ι → Scheme.{u}} {Z : Scheme.{u}} (f : ∀ k, Y k ⟶ Z) (hs : IsColimit (Cofan.mk Z f))
    [∀ k, CompactSpace (Y k)] [∀ k, QuasiSeparatedSpace (Y k)] :
    CompactSpace Z ∧ QuasiSeparatedSpace Z := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let ε : ULift.{u} (Fin n) ≃ ι := Equiv.ulift.trans e.symm
  let Y' : ULift.{u} (Fin n) → Scheme.{u} := Y ∘ ε
  let iso : Z ≅ ∐ Y' :=
    hs.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫ (Sigma.reindex ε Y).symm
  let h : (Σ k, Y' k) ≃ₜ Z := (sigmaMk Y').trans iso.inv.homeomorph
  have : ∀ k, CompactSpace (Y' k) := fun k ↦ inferInstanceAs (CompactSpace (Y (ε k)))
  have : ∀ k, QuasiSeparatedSpace (Y' k) := fun k ↦
    inferInstanceAs (QuasiSeparatedSpace (Y (ε k)))
  exact ⟨h.compactSpace, (quasiSeparatedSpace_congr h).mp quasiSeparatedSpace_sigma⟩

/-- The apex of a finite coproduct in `X.Etale` of quasi-compact quasi-separated schemes is
quasi-compact and quasi-separated. -/
lemma Scheme.Etale.compactSpace_quasiSeparatedSpace_of_isColimit {X : Scheme.{u}} {ι : Type}
    [Finite ι] {Y : ι → X.Etale} {Z : X.Etale} (f : ∀ k, Y k ⟶ Z)
    (hs : IsColimit (Cofan.mk Z f))
    (hY : ∀ k, CompactSpace (Y k).left ∧ QuasiSeparatedSpace (Y k).left) :
    CompactSpace Z.left ∧ QuasiSeparatedSpace Z.left := by
  let Yl : ι → Scheme.{u} := fun k ↦ (Y k).left
  let p : ∀ k, Yl k ⟶ X := fun k ↦ (Y k).hom
  let W : X.Etale := MorphismProperty.Over.mk ⊤ (Sigma.desc p)
    (IsZariskiLocalAtSource.sigmaDesc fun k ↦ (Y k).prop)
  let ιW : ∀ k, Y k ⟶ W := fun k ↦
    MorphismProperty.Over.homMk (Sigma.ι Yl k) (Sigma.ι_desc p k)
  have hW : IsColimit (Cofan.mk W ιW) := Cofan.IsColimit.mk _
    (fun s ↦ MorphismProperty.Over.homMk (Sigma.desc fun k ↦ (s.inj k).left) (by
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      rw [Sigma.ι_desc_assoc]
      exact (MorphismProperty.Over.w (s.inj k)).trans (Sigma.ι_desc p k).symm))
    (fun s k ↦ MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ k))
    (fun s m hm ↦ MorphismProperty.Over.Hom.ext (Sigma.hom_ext _ _ fun k ↦
      (congrArg (fun φ ↦ φ.left) (hm k)).trans
        (Sigma.ι_desc (fun k ↦ (s.inj k).left) k).symm))
  let e := (Scheme.Etale.forget X ⋙ Over.forget X).mapIso (hs.coconePointUniqueUpToIso hW)
  have : ∀ k, CompactSpace (Yl k) := fun k ↦ (hY k).1
  have : ∀ k, QuasiSeparatedSpace (Yl k) := fun k ↦ (hY k).2
  obtain ⟨h₁, h₂⟩ := Scheme.compactSpace_quasiSeparatedSpace_of_isColimit (Sigma.ι Yl)
    (coproductIsCoproduct Yl)
  have h : W.left ≃ₜ Z.left := e.inv.homeomorph
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h₁ h, (quasiSeparatedSpace_congr h).mp h₂⟩

/-- An étale scheme over a quasi-compact quasi-separated base whose underlying space is
quasi-compact and quasi-separated is qcqs étale. -/
lemma isQcqsEtale_of_compactSpace {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : X.Etale) [hZ : CompactSpace Z.left] [hZ' : QuasiSeparatedSpace Z.left] :
    IsQcqsEtale ((Scheme.Etale.forget X).obj Z) :=
  ⟨Z.prop, inferInstanceAs (LocallyOfFinitePresentation Z.hom),
    @quasiCompact_of_compactSpace _ X Z.hom hZ _,
    @QuasiSeparated.of_quasiSeparatedSpace _ X Z.hom hZ'⟩

instance SimplexCategory.Truncated.finite (r : ℕ) : Finite (SimplexCategory.Truncated r) :=
  Finite.of_injective (fun Δ : SimplexCategory.Truncated r ↦
    (⟨Δ.obj.len, Nat.lt_succ_of_le Δ.property⟩ : Fin (r + 1))) (by
      rintro ⟨⟨a⟩, ha⟩ ⟨⟨b⟩, hb⟩ hab
      simp only [Fin.mk.injEq] at hab
      subst hab
      rfl)

instance SimplexCategory.Truncated.finite_op (r : ℕ) :
    Finite (SimplexCategory.Truncated r)ᵒᵖ :=
  Finite.of_injective (fun Δ : (SimplexCategory.Truncated r)ᵒᵖ ↦ Δ.unop)
    (fun _ _ h ↦ Opposite.unop_injective h)

instance SimplexCategory.Truncated.finite_hom {r : ℕ} (a b : SimplexCategory.Truncated r) :
    Finite (a ⟶ b) :=
  Finite.of_injective (fun f : a ⟶ b ↦ f.hom) (fun _ _ h ↦ ObjectProperty.hom_ext _ h)

instance SimplexCategory.Truncated.finite_hom_op {r : ℕ}
    (a b : (SimplexCategory.Truncated r)ᵒᵖ) : Finite (a ⟶ b) :=
  Finite.of_injective (fun f : a ⟶ b ↦ f.unop) (fun _ _ h ↦ Quiver.Hom.unop_inj h)

namespace TruncatedFiniteSplitEtaleHypercover

variable {X : Scheme.{u}} {r : ℕ} (U : TruncatedFiniteSplitEtaleHypercover X r)

lemma compactSpace_N (n : Fin (r + 1)) :
    CompactSpace (U.N n).left ∧ QuasiSeparatedSpace (U.N n).left := by
  obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
  exact Scheme.Etale.compactSpace_quasiSeparatedSpace_of_isColimit ι hι
    fun i ↦ ⟨(hV i).1, (hV i).2.1⟩

lemma compactSpace_obj (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
    CompactSpace (U.simplicial.obj Δ).left ∧ QuasiSeparatedSpace (U.simplicial.obj Δ).left :=
  Scheme.Etale.compactSpace_quasiSeparatedSpace_of_isColimit _ (U.splitting Δ)
    fun a ↦ U.compactSpace_N a.1

lemma isQcqsEtale_diagram_obj [CompactSpace X] [QuasiSeparatedSpace X]
    (Δ : (SimplexCategory.Truncated r)ᵒᵖ) : IsQcqsEtale (U.diagram.obj Δ) := by
  obtain ⟨_, _⟩ := U.compactSpace_obj Δ
  exact isQcqsEtale_of_compactSpace (U.simplicial.obj Δ)

end TruncatedFiniteSplitEtaleHypercover

section Transport

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Base change along a composite transition map is base change along the two maps in turn. -/
noncomputable def overPullbackCompIso {i j k : I} (h : j ⟶ i) (g : k ⟶ j) :
    Over.pullback (D.map (g ≫ h)) ≅ Over.pullback (D.map h) ⋙ Over.pullback (D.map g) :=
  eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp g h)) ≪≫ Over.pullbackComp _ _

set_option linter.flexible false in
private lemma eqToHom_pullbackComp_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (f' : X ⟶ Z) (hf : f' = f ≫ g) (U : Over Z) :
    ((eqToHom (congrArg (fun k : X ⟶ Z ↦ Over.pullback k) hf)).app U ≫
        (Over.pullbackComp f g).hom.app U).left ≫
      pullback.fst _ f ≫ pullback.fst U.hom g = pullback.fst U.hom f' := by
  subst hf
  simp only [Over.pullback_obj_left, Functor.comp_obj, Over.pullback_obj_hom]
  simp [Over.pullbackComp, Over.mapComp, conjugateIsoEquiv, conjugateEquiv]
  exact (Category.id_comp _).trans (Category.id_comp _)

@[reassoc (attr := simp)]
lemma overPullbackCompIso_hom_app_left_fst {i j k : I} (h : j ⟶ i) (g : k ⟶ j)
    (U : Over (D.obj i)) :
    ((overPullbackCompIso D h g).hom.app U).left ≫ pullback.fst _ (D.map g) ≫
      pullback.fst U.hom (D.map h) = pullback.fst U.hom (D.map (g ≫ h)) :=
  eqToHom_pullbackComp_left_fst _ _ _ (D.map_comp g h) U

@[reassoc (attr := simp)]
lemma overPullbackCompIso_hom_app_left_snd {i j k : I} (h : j ⟶ i) (g : k ⟶ j)
    (U : Over (D.obj i)) :
    ((overPullbackCompIso D h g).hom.app U).left ≫ pullback.snd _ (D.map g) =
      pullback.snd U.hom (D.map (g ≫ h)) :=
  Over.w ((overPullbackCompIso D h g).hom.app U)

lemma overPullbackStageIso_comp {i j k : I} (h : j ⟶ i) (g : k ⟶ j) (U : Over (D.obj i)) :
    (overPullbackStageIso D c (g ≫ h)).hom.app U =
      (Over.pullback (c.π.app k)).map ((overPullbackCompIso D h g).hom.app U) ≫
        (overPullbackStageIso D c g).hom.app ((Over.pullback (D.map h)).obj U) ≫
          (overPullbackStageIso D c h).hom.app U := by
  ext : 1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      overPullbackStageIso_hom_app_left_fst, overPullbackStageIso_hom_app_left_fst_assoc]
    erw [pullback.lift_fst_assoc]
    rw [Category.assoc, overPullbackCompIso_hom_app_left_fst]
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      overPullbackStageIso_hom_app_left_snd]
    erw [pullback.lift_snd]

end Transport

section Finite

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Equalities of natural transformations between finite diagrams of qcqs étale schemes descend
eventually. -/
theorem stageEventually_whiskerRight_eq {C : Type*} [Category* C] [Finite C] {i : I}
    {F G : C ⥤ Over (D.obj i)} (hF : ∀ a, IsQcqsEtale (F.obj a))
    (hG : ∀ a, IsQcqsEtale (G.obj a)) (φ ψ : F ⟶ G)
    (h : Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
      Functor.whiskerRight ψ (Over.pullback (c.π.app i))) :
    StageEventually i (fun _ h ↦ Functor.whiskerRight φ (Over.pullback (D.map h)) =
      Functor.whiskerRight ψ (Over.pullback (D.map h))) := by
  refine (StageEventually.finite_forall (Q := fun a _ h ↦
      (Over.pullback (D.map h)).map (φ.app a) =
      (Over.pullback (D.map h)).map (ψ.app a)) fun a ↦ ?_).mono fun _ _ H ↦ ?_
  · obtain ⟨_, _, _, _⟩ := hF a
    obtain ⟨_, _, _, _⟩ := hG a
    exact stageEventually_overPullback_map_eq D hc _ _ (φ.app a) (ψ.app a)
      (congrArg (fun τ ↦ τ.app a) h)
  · refine NatTrans.ext (funext fun a ↦ ?_)
    exact H a

include hc in
/-- Natural transformations between the base changes to the limit of finite diagrams of qcqs
étale schemes over a stage descend to a later stage. -/
theorem exists_natTrans_descent {C : Type*} [Category* C] [Finite C]
    [∀ a b : C, Finite (a ⟶ b)] {i : I}
    {F G : C ⥤ Over (D.obj i)} (hF : ∀ a, IsQcqsEtale (F.obj a))
    (hG : ∀ a, IsQcqsEtale (G.obj a))
    (φ : F ⋙ Over.pullback (c.π.app i) ⟶ G ⋙ Over.pullback (c.π.app i)) :
    ∃ (j : I) (h : j ⟶ i)
      (ψ : F ⋙ Over.pullback (D.map h) ⟶ G ⋙ Over.pullback (D.map h)),
      ∀ a, (Over.pullback (c.π.app j)).map (ψ.app a) ≫
          (overPullbackStageIso D c h).hom.app (G.obj a) =
        (overPullbackStageIso D c h).hom.app (F.obj a) ≫ φ.app a := by
  obtain ⟨j₁, h₁, H₁⟩ := (StageEventually.finite_forall (fun a : C ↦ by
    obtain ⟨_, _, _, _⟩ := hF a
    obtain ⟨_, _, _, _⟩ := hG a
    exact stageEventually_exists_overPullback_hom D hc (F.obj a) (G.obj a)
      (φ.app a))).exists_hom
  choose ψ₁ hψ₁ using H₁
  have hnat : ∀ x : Σ a b : C, a ⟶ b,
      (Over.pullback (c.π.app j₁)).map ((Over.pullback (D.map h₁)).map (F.map x.2.2) ≫
        ψ₁ x.2.1) =
      (Over.pullback (c.π.app j₁)).map (ψ₁ x.1 ≫ (Over.pullback (D.map h₁)).map
        (G.map x.2.2)) := by
    rintro ⟨a, b, f⟩
    rw [← cancel_mono ((overPullbackStageIso D c h₁).hom.app (G.obj b))]
    have n1 := (overPullbackStageIso D c h₁).hom.naturality (F.map f)
    have n2 := (overPullbackStageIso D c h₁).hom.naturality (G.map f)
    have n3 := φ.naturality f
    simp only [Functor.comp_map] at n1 n2 n3
    simp only [Functor.map_comp, Category.assoc, hψ₁, reassoc_of% n1, n2,
      reassoc_of% (hψ₁ a), n3]
  obtain ⟨j₂, g, H₂⟩ := (StageEventually.finite_forall (fun x : Σ a b : C, a ⟶ b ↦ by
    obtain ⟨_, _, _, _⟩ := (hF x.1).overPullback (D.map h₁)
    obtain ⟨_, _, _, _⟩ := (hG x.2.1).overPullback (D.map h₁)
    exact stageEventually_overPullback_map_eq D hc _ _ _ _ (hnat x))).exists_hom
  let τ := overPullbackCompIso D h₁ g
  refine ⟨j₂, g ≫ h₁,
    { app := fun a ↦ τ.hom.app (F.obj a) ≫ (Over.pullback (D.map g)).map (ψ₁ a) ≫
        τ.inv.app (G.obj a)
      naturality := fun a b f ↦ ?_ }, fun a ↦ ?_⟩
  · have n1 := τ.hom.naturality (F.map f)
    have n2 := τ.inv.naturality (G.map f)
    have n3 := H₂ ⟨a, b, f⟩
    simp only [Functor.comp_map, Functor.map_comp] at n1 n2 n3 ⊢
    simp only [reassoc_of% n1, reassoc_of% n3, Category.assoc, n2]
  · have n1 := (overPullbackStageIso D c g).hom.naturality (ψ₁ a)
    simp only [Functor.comp_map] at n1
    rw [overPullbackStageIso_comp, overPullbackStageIso_comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (Over.pullback (c.π.app j₂)) (τ.inv.app (G.obj a)),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% n1, hψ₁]

end Finite

end AlgebraicGeometry
