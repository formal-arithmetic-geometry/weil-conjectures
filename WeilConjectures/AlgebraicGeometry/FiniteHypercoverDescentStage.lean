/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteCoproducts
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
public import WeilConjectures.AlgebraicGeometry.FiniteDiagramDescent
public import WeilConjectures.AlgebraicGeometry.TruncatedMatchingObject

/-!
# Stage data for the descent of truncated finite split étale hypercovers

Given a truncated finite split étale hypercover `U` of the limit `c.pt` of a cofiltered system
`D` of qcqs schemes with affine transition maps, we descend the underlying diagram, the
nondegenerate summands and their inclusions to a stage (`HypercoverStageData`), and record that
such data can be transported to later stages.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The class of étale, quasi-compact and quasi-separated morphisms of schemes. -/
abbrev qcqsEtale : MorphismProperty Scheme.{u} :=
  (@Etale : MorphismProperty Scheme.{u}) ⊓ ((@QuasiCompact : MorphismProperty Scheme.{u}) ⊓
    (@QuasiSeparated : MorphismProperty Scheme.{u}))

instance : (qcqsEtale.{u}).HasOfPostcompProperty qcqsEtale.{u} := by
  have : MorphismProperty.HasOfPostcompProperty (@Etale : MorphismProperty Scheme.{u})
      qcqsEtale.{u} :=
    .of_le _ _ inf_le_left
  have : MorphismProperty.HasOfPostcompProperty (@QuasiCompact : MorphismProperty Scheme.{u})
      qcqsEtale.{u} :=
    .of_le _ (@QuasiSeparated : MorphismProperty Scheme.{u})
      (inf_le_right.trans inf_le_right)
  have : MorphismProperty.HasOfPostcompProperty
      (@QuasiSeparated : MorphismProperty Scheme.{u}) qcqsEtale.{u} :=
    .of_le _ ⊤ le_top
  infer_instance

lemma qcqsEtale_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    qcqsEtale f ↔ Etale f ∧ QuasiCompact f ∧ QuasiSeparated f := Iff.rfl

lemma IsQcqsEtale.qcqsEtale {X : Scheme.{u}} {U : Over X} (hU : IsQcqsEtale U) :
    qcqsEtale U.hom :=
  ⟨hU.1, hU.2.2.1, hU.2.2.2⟩

lemma isQcqsEtale_of_qcqsEtale {X : Scheme.{u}} {U : Over X} (hU : qcqsEtale U.hom) :
    IsQcqsEtale U := by
  obtain ⟨h₁, h₂, h₃⟩ := hU
  exact ⟨h₁, inferInstance, h₂, h₃⟩

/-- The top simplex `[n]` of the `r`-truncated simplex category. -/
abbrev truncTop {r : ℕ} (n : Fin (r + 1)) : SimplexCategory.Truncated r :=
  ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩

/-- Transport of a coproduct cofan along isomorphisms of the summands and of the apex. -/
noncomputable def Cofan.isColimitOfIsos {C : Type*} [Category* C] {ι : Type*}
    {A A' : ι → C} {Z Z' : C} {f : ∀ k, A k ⟶ Z} {f' : ∀ k, A' k ⟶ Z'}
    (hZ : IsColimit (Cofan.mk Z f)) (b : ∀ k, A' k ≅ A k) (z : Z' ≅ Z)
    (hf : ∀ k, f' k ≫ z.hom = (b k).hom ≫ f k) : IsColimit (Cofan.mk Z' f') :=
  Cofan.IsColimit.mk _ (fun s ↦ z.hom ≫ Cofan.IsColimit.desc hZ fun k ↦ (b k).inv ≫ s.inj k)
    (fun s k ↦ by
      change f' k ≫ _ ≫ _ = _
      rw [reassoc_of% (hf k)]
      erw [Cofan.IsColimit.fac hZ _ k]
      simp)
    (fun s m hm ↦ by
      rw [← Iso.inv_comp_eq]
      refine Cofan.IsColimit.hom_ext hZ _ _ fun k ↦ ?_
      have : f k ≫ z.inv = (b k).inv ≫ f' k := by
        rw [Iso.comp_inv_eq, Category.assoc, hf k, Iso.inv_hom_id_assoc]
      erw [Cofan.IsColimit.fac hZ _ k]
      change f k ≫ z.inv ≫ m = _
      rw [reassoc_of% this]
      erw [hm k])

/-- A coproduct cofan stays a coproduct after replacing the legs by equal ones. -/
noncomputable def Cofan.isColimitCongr {C : Type*} [Category* C] {ι : Type*}
    {A : ι → C} {Z : C} {f g : ∀ k, A k ⟶ Z} (h : ∀ k, f k = g k)
    (hf : IsColimit (Cofan.mk Z f)) : IsColimit (Cofan.mk Z g) :=
  (funext h) ▸ hf

/-- A one-term cofan with identity leg is a coproduct. -/
noncomputable def Cofan.isColimitId {C : Type*} [Category* C] (Z : C) :
    IsColimit (Cofan.mk Z fun _ : Fin 1 ↦ 𝟙 Z) :=
  Cofan.IsColimit.mk _ (fun s ↦ s.inj 0)
    (fun s k ↦ by
      obtain rfl := Subsingleton.elim k 0
      exact Category.id_comp _)
    (fun s m hm ↦ (Category.id_comp m).symm.trans (hm 0))

/-- Base change preserves surjectivity of morphisms in `Over S`. -/
lemma surjective_overPullback_map_left {S T : Scheme.{u}} (g : T ⟶ S) {A B : Over S}
    (φ : A ⟶ B) (hφ : Surjective φ.left) : Surjective ((Over.pullback g).map φ).left := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := hφ.surj (pullback.fst B.hom g x)
  exact exists_overPullback_map_left_eq g φ x z hz

section Stage

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) {r : ℕ}
  (U : TruncatedFiniteSplitEtaleHypercover c.pt r)

/-- Descent data of a truncated finite split étale hypercover over the limit at a stage: the
underlying diagram, the nondegenerate summands and their inclusions, with identifications of
their base changes to the limit. -/
structure HypercoverStageData (i : I) where
  /-- The diagram at the stage. -/
  G : (SimplexCategory.Truncated r)ᵒᵖ ⥤ Over (D.obj i)
  hG : ∀ a, IsQcqsEtale (G.obj a)
  /-- The identification of the base change of the diagram. -/
  e : G ⋙ Over.pullback (c.π.app i) ≅ U.diagram
  /-- The nondegenerate summands at the stage. -/
  N : Fin (r + 1) → Over (D.obj i)
  hN : ∀ n, IsQcqsEtale (N n)
  /-- The identification of the base changes of the summands. -/
  a : ∀ n, (Over.pullback (c.π.app i)).obj (N n) ≅ (Scheme.Etale.forget c.pt).obj (U.N n)
  /-- The inclusions of the summands at the stage. -/
  ι : ∀ n, N n ⟶ G.obj (op (truncTop n))
  hι : ∀ n, (Over.pullback (c.π.app i)).map (ι n) ≫ e.hom.app (op (truncTop n)) =
    (a n).hom ≫ (Scheme.Etale.forget c.pt).map (U.inclusion n)

namespace HypercoverStageData

variable {D c U}

/-- Transport of stage data along a transition map. -/
noncomputable def transport {i j : I} (S : HypercoverStageData D c U i) (h : j ⟶ i) :
    HypercoverStageData D c U j where
  G := S.G ⋙ Over.pullback (D.map h)
  hG a := (S.hG a).overPullback _
  e := Functor.isoWhiskerLeft S.G (overPullbackStageIso D c h) ≪≫ S.e
  N n := (Over.pullback (D.map h)).obj (S.N n)
  hN n := (S.hN n).overPullback _
  a n := (overPullbackStageIso D c h).app (S.N n) ≪≫ S.a n
  ι n := (Over.pullback (D.map h)).map (S.ι n)
  hι n := by
    have nat := (overPullbackStageIso D c h).hom.naturality (S.ι n)
    simp only [Functor.comp_map] at nat
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Iso.app_hom, Category.assoc]
    rw [reassoc_of% nat, S.hι n]

end HypercoverStageData

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c} (hc : IsLimit c)

include hc in
/-- The diagram, the nondegenerate summands and their inclusions of a truncated finite split
étale hypercover over the limit descend to a stage. -/
theorem exists_hypercoverStageData : ∃ i, Nonempty (HypercoverStageData D c U i) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  obtain ⟨i₁, G₀, hG₀, ⟨e₀⟩⟩ := exists_functor_descent D hc U.diagram
    U.isQcqsEtale_diagram_obj
  obtain ⟨i₂, N₀, hN₀, ⟨a₀⟩⟩ := exists_objects_descent D hc
    (fun n ↦ (Scheme.Etale.forget c.pt).obj (U.N n)) (fun n ↦ by
      obtain ⟨_, _⟩ := U.compactSpace_N n
      exact isQcqsEtale_of_compactSpace (U.N n))
  let k := IsCofiltered.min i₁ i₂
  let G : (SimplexCategory.Truncated r)ᵒᵖ ⥤ Over (D.obj k) :=
    G₀ ⋙ Over.pullback (D.map (IsCofiltered.minToLeft i₁ i₂))
  have hG : ∀ a, IsQcqsEtale (G.obj a) := fun a ↦ (hG₀ a).overPullback _
  let e : G ⋙ Over.pullback (c.π.app k) ≅ U.diagram :=
    Functor.isoWhiskerLeft G₀ (overPullbackStageIso D c _) ≪≫ e₀
  let N : Fin (r + 1) → Over (D.obj k) := fun n ↦
    (Over.pullback (D.map (IsCofiltered.minToRight i₁ i₂))).obj (N₀ n)
  have hN : ∀ n, IsQcqsEtale (N n) := fun n ↦ (hN₀ n).overPullback _
  let a : ∀ n, (Over.pullback (c.π.app k)).obj (N n) ≅
      (Scheme.Etale.forget c.pt).obj (U.N n) := fun n ↦
    (overPullbackStageIso D c _).app (N₀ n) ≪≫ a₀ n
  let ψ : ∀ n, (Over.pullback (c.π.app k)).obj (N n) ⟶
      (Over.pullback (c.π.app k)).obj (G.obj (op (truncTop n))) := fun n ↦
    (a n).hom ≫ (Scheme.Etale.forget c.pt).map (U.inclusion n) ≫
      e.inv.app (op (truncTop n))
  obtain ⟨k₁, h₁, H⟩ := (StageEventually.finite_forall fun n : Fin (r + 1) ↦ by
    obtain ⟨_, _, _, _⟩ := hN n
    obtain ⟨_, _, _, _⟩ := hG (op (truncTop n))
    exact stageEventually_exists_overPullback_hom D hc _ _ (ψ n)).exists_hom
  choose φ hφ using H
  refine ⟨k₁, ⟨
    { G := G ⋙ Over.pullback (D.map h₁)
      hG := fun a ↦ (hG a).overPullback _
      e := Functor.isoWhiskerLeft G (overPullbackStageIso D c h₁) ≪≫ e
      N := fun n ↦ (Over.pullback (D.map h₁)).obj (N n)
      hN := fun n ↦ (hN n).overPullback _
      a := fun n ↦ (overPullbackStageIso D c h₁).app (N n) ≪≫ a n
      ι := φ
      hι := fun n ↦ ?_ }⟩⟩
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.app_hom]
  rw [reassoc_of% (hφ n)]
  simp only [ψ, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg _ (congrArg _ (Category.comp_id _))

end Stage

end AlgebraicGeometry
