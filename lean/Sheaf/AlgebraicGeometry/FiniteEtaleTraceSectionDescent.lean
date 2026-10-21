/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSheetLifting
import WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitCover

/-! # Descent of the sum of sheet coordinates -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V S : Scheme.{u}} (p : V ⟶ S)
  (L : SheafOfModules.{u + 1} (traceFieldRing l E S))

private def traceCoordinate [Etale p] {U : S.ProEt} {J : Type u} [Finite J]
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    L.val.obj (op (AsSmall.up.obj B)) :=
  (Equiv.ofBijective (fun t ↦ traceImageSheetUnit l E p L σ h j t)
    ((finiteEtaleTrace_sheet_lifting l E p L σ h).1 j)).symm
      (traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L) s)

private theorem traceCoordinate_spec [Etale p] {U : S.ProEt} {J : Type u} [Finite J]
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    traceImageSheetUnit l E p L σ h j (traceCoordinate l E p L σ h j s) =
      traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L) s :=
  (Equiv.ofBijective _ ((finiteEtaleTrace_sheet_lifting l E p L σ h).1 j)).apply_symm_apply _

private theorem traceCoordinate_naturality [Etale p]
    {U : S.ProEt} {J : Type u} [Finite J] (σ : TraceImageSplitting p U J)
    {B C : S.ProEt} (h : B ⟶ U) (a : C ⟶ B) (j : J)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    L.val.map (AsSmall.up.map a).op (traceCoordinate l E p L σ h j s) =
      traceCoordinate l E p L σ (a ≫ h) j
        (((traceModulePullback l E p).obj L).val.map
          (AsSmall.up.map ((proEtaleBaseChange p).map a)).op s) := by
  let P := (traceModulePullback l E p).obj L
  let d : traceImageSheetObject σ (a ≫ h) j ⟶ traceImageSheetObject σ h j :=
    MorphismProperty.Over.homMk a.left (by
      change a.left ≫ (h.left ≫ σ.sheet j) = (a ≫ h).left ≫ σ.sheet j
      exact (Category.assoc _ _ _).symm)
  have hd : d ≫ traceImageSheetArrow σ h j =
      traceImageSheetArrow σ (a ≫ h) j ≫ (proEtaleBaseChange p).map a := by
    apply MorphismProperty.Over.Hom.ext
    change a.left ≫ (traceImageSheetArrow σ h j).left =
      (traceImageSheetArrow σ (a ≫ h) j).left ≫ ((proEtaleBaseChange p).map a).left
    apply pullback.hom_ext
    · change (a.left ≫ pullback.lift (𝟙 _) (h.left ≫ σ.sheet j) _) ≫
          pullback.fst B.hom p =
        (pullback.lift (𝟙 _) ((a ≫ h).left ≫ σ.sheet j) _) ≫
          (pullback.lift (pullback.fst C.hom p ≫ a.left) (pullback.snd C.hom p) _) ≫
            pullback.fst B.hom p
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.id_comp, Category.comp_id]
    · change (a.left ≫ pullback.lift (𝟙 _) (h.left ≫ σ.sheet j) _) ≫
          pullback.snd B.hom p =
        (pullback.lift (𝟙 _) ((a ≫ h).left ≫ σ.sheet j) _) ≫
          (pullback.lift (pullback.fst C.hom p ≫ a.left) (pullback.snd C.hom p) _) ≫
            pullback.snd B.hom p
      simp only [Category.assoc, pullback.lift_snd]
      exact (Category.assoc _ _ _).symm
  apply ((finiteEtaleTrace_sheet_lifting l E p L σ (a ≫ h)).1 j).injective
  dsimp only
  rw [traceCoordinate_spec]
  unfold traceImageSheetUnit traceImageSheetRestriction
  have hn := PresheafOfModules.naturality_apply
    ((SheafOfModules.pullbackPushforwardAdjunction
      (traceFieldRingMap l E p)).unit.app L).val (AsSmall.up.map a).op
        (traceCoordinate l E p L σ h j s)
  erw [hn]
  have hh := traceCoordinate_spec l E p L σ h j s
  unfold traceImageSheetUnit traceImageSheetRestriction at hh
  have hh' := congrArg (fun z ↦ P.val.presheaf.map (AsSmall.up.map d).op z) hh
  change P.val.presheaf.map (AsSmall.up.map d).op
    (P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ h j)).op _) =
      P.val.presheaf.map (AsSmall.up.map d).op
        (P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ h j)).op s) at hh'
  change P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ (a ≫ h) j)).op
    (P.val.presheaf.map (AsSmall.up.map ((proEtaleBaseChange p).map a)).op _) =
      P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ (a ≫ h) j)).op
        (P.val.presheaf.map (AsSmall.up.map ((proEtaleBaseChange p).map a)).op s)
  have he : (AsSmall.up.map ((proEtaleBaseChange p).map a)).op ≫
      (AsSmall.up.map (traceImageSheetArrow σ (a ≫ h) j)).op =
      (AsSmall.up.map (traceImageSheetArrow σ h j)).op ≫ (AsSmall.up.map d).op := by
    rw [← op_comp, ← op_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, hd]
  simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] at hh' ⊢
  rw [he]
  exact hh'

private def traceSheetCoproduct {U : S.ProEt} {J : Type u} [Fintype J]
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) :
    IsColimit (Cofan.mk ((proEtaleBaseChange p).obj B).left
      (fun j ↦ (traceImageSheetArrow σ h j).left)) := by
  let b : pullback B.hom p ⟶ pullback U.hom p := ((proEtaleBaseChange p).map h).left
  let a (j : J) : B.left ⟶ pullback B.hom p :=
    pullback.lift (𝟙 _) (h.left ≫ σ.sheet j) (by simp [Category.assoc, σ.over])
  let i (j : J) : U.left ⟶ pullback U.hom p :=
    pullback.lift (𝟙 U.left) (σ.sheet j) (by simp [σ.over])
  have hb₁ : b ≫ pullback.fst U.hom p = pullback.fst B.hom p ≫ h.left := by
    simp [b, MorphismProperty.Over.pullback_map_left]
  have hb₂ : b ≫ pullback.snd U.hom p = pullback.snd B.hom p := by
    simp [b, MorphismProperty.Over.pullback_map_left]
  have hab (j : J) : a j ≫ b = h.left ≫ i j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hb₁, a, pullback.lift_fst_assoc, i,
        pullback.lift_fst, Category.comp_id]
      exact Category.id_comp _
    · simp only [Category.assoc, hb₂, a, pullback.lift_snd, i, pullback.lift_snd]
  have hl (j : J) : IsLimit (PullbackCone.mk (a j) h.left (hab j)) := by
    refine PullbackCone.IsLimit.mk _ (fun c ↦ c.fst ≫ pullback.fst B.hom p) ?_ ?_ ?_
    · intro c
      have hs : c.fst ≫ pullback.fst B.hom p ≫ h.left = c.snd := by
        rw [← hb₁, ← Category.assoc, c.condition]
        simp [i]
      apply pullback.hom_ext
      · simp only [a, Category.assoc, pullback.lift_fst, Category.comp_id]
      · change (c.fst ≫ pullback.fst B.hom p) ≫ a j ≫
          pullback.snd B.hom p = c.fst ≫ pullback.snd B.hom p
        simp only [a, pullback.lift_snd]
        calc
          _ = (c.fst ≫ pullback.fst B.hom p ≫ h.left) ≫ σ.sheet j := by
            simp only [Category.assoc]
          _ = c.snd ≫ σ.sheet j := by rw [hs]
          _ = c.snd ≫ i j ≫ pullback.snd U.hom p := by simp [i]
          _ = c.fst ≫ b ≫ pullback.snd U.hom p := by
            rw [← Category.assoc, ← c.condition, Category.assoc]
          _ = _ := by rw [hb₂]
    · intro c
      simp only [Category.assoc]
      rw [← hb₁, ← Category.assoc, c.condition]
      simp [i]
    · intro c m hm _
      have hh := congrArg (fun k ↦ k ≫ pullback.fst B.hom p) hm
      simpa only [Category.assoc, a, pullback.lift_fst, Category.comp_id] using hh
  let hu := FinitaryPreExtensive.isUniversal_finiteCoproducts σ.coproduct
  exact (hu.nonempty_isColimit_of_pullbackCone_left i (𝟙 _) b
    (fun j ↦ PullbackCone.mk (a j) h.left (hab j)) hl
    (PullbackCone.mk (𝟙 _) b (by simp))
    (PullbackCone.IsLimit.mk _ (fun c ↦ c.fst) (by simp)
      (by intro c; simpa using c.condition) (by intro c m hm _; exact hm))
    (Cofan.mk _ a) (Iso.refl _) (by intro j; rfl) (by intro j; rfl)
      (by intro j; exact hab j)).some


private theorem traceCoordinate_eq_of_sheet [Etale p]
    {U₁ U₂ B : S.ProEt} {J₁ J₂ : Type u} [Finite J₁] [Finite J₂]
    (σ₁ : TraceImageSplitting p U₁ J₁) (σ₂ : TraceImageSplitting p U₂ J₂)
    (h₁ : B ⟶ U₁) (h₂ : B ⟶ U₂) (j : J₁) (k : J₂)
    (he : h₁.left ≫ σ₁.sheet j = h₂.left ≫ σ₂.sheet k)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    traceCoordinate l E p L σ₁ h₁ j s = traceCoordinate l E p L σ₂ h₂ k s := by
  let P := (traceModulePullback l E p).obj L
  let d : traceImageSheetObject σ₁ h₁ j ⟶ traceImageSheetObject σ₂ h₂ k :=
    MorphismProperty.Over.homMk (𝟙 B.left) (by
      change 𝟙 _ ≫ (h₂.left ≫ σ₂.sheet k) = h₁.left ≫ σ₁.sheet j
      simpa only [Category.id_comp] using he.symm)
  have hd : d ≫ traceImageSheetArrow σ₂ h₂ k = traceImageSheetArrow σ₁ h₁ j := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 B.left) ≫ (traceImageSheetArrow σ₂ h₂ k).left =
      (traceImageSheetArrow σ₁ h₁ j).left
    rw [Category.id_comp]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans
        (he.symm.trans (pullback.lift_snd _ _ _).symm)
  apply ((finiteEtaleTrace_sheet_lifting l E p L σ₁ h₁).1 j).injective
  dsimp only
  rw [traceCoordinate_spec]
  have hh := congrArg (fun z ↦ P.val.presheaf.map (AsSmall.up.map d).op z)
    (traceCoordinate_spec l E p L σ₂ h₂ k s)
  unfold traceImageSheetUnit traceImageSheetRestriction at hh ⊢
  change P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ₁ h₁ j)).op s =
    P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ₁ h₁ j)).op _
  change P.val.presheaf.map (AsSmall.up.map d).op
    (P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ₂ h₂ k)).op _) =
      P.val.presheaf.map (AsSmall.up.map d).op
        (P.val.presheaf.map (AsSmall.up.map (traceImageSheetArrow σ₂ h₂ k)).op s) at hh
  have he' : (AsSmall.up.map (traceImageSheetArrow σ₂ h₂ k)).op ≫
      (AsSmall.up.map d).op = (AsSmall.up.map (traceImageSheetArrow σ₁ h₁ j)).op := by
    rw [← op_comp, ← CategoryTheory.Functor.map_comp, hd]
  simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] at hh
  rw [he'] at hh
  exact hh.symm

private theorem traceCoordinate_sum_eq [Etale p]
    {U₁ U₂ B : S.ProEt} {J₁ J₂ : Type u} [Fintype J₁] [Fintype J₂]
    (σ₁ : TraceImageSplitting p U₁ J₁) (σ₂ : TraceImageSplitting p U₂ J₂)
    (h₁ : B ⟶ U₁) (h₂ : B ⟶ U₂)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    (∑ j, traceCoordinate l E p L σ₁ h₁ j s) =
      ∑ k, traceCoordinate l E p L σ₂ h₂ k s := by
  classical
  let a₁ (j : J₁) := (traceImageSheetArrow σ₁ h₁ j).left
  let a₂ (j : J₂) := (traceImageSheetArrow σ₂ h₂ j).left
  have hlocal (x : B.left) : ∃ W : B.left.Opens, x ∈ W ∧ ∃ e : J₁ ≃ J₂,
      ∀ j, W.ι ≫ a₁ j = W.ι ≫ a₂ (e j) := by
    apply finiteSectionCoproduct_local_permutation B.left (pullback B.hom p)
      (pullback.fst B.hom p) J₁ J₂ a₁ a₂
      (traceSheetCoproduct p σ₁ h₁) (traceSheetCoproduct p σ₂ h₂)
      (fun j ↦ pullback.lift_fst _ _ _) (fun j ↦ pullback.lift_fst _ _ _) x
  choose W hW e hsections using hlocal
  let D (x : B.left) : S.ProEt := ProEt.mk ((W x).ι ≫ B.hom)
  let a (x : B.left) : D x ⟶ B := MorphismProperty.Over.homMk (W x).ι rfl
  have hopen (x : B.left) : IsOpenImmersion (a x).left := by
    change IsOpenImmersion (W x).ι
    infer_instance
  have hcover : ∀ y : B.left, ∃ x z, (a x).left z = y := by
    intro y
    exact ⟨y, ⟨y, hW y⟩, rfl⟩
  have hmem : Presieve.ofArrows D a ∈ ProEt.precoverage S B := by
    change (Presieve.ofArrows D a).map (ProEt.forget S ⋙ Over.forget S) ∈
      proetalePrecoverage B.left
    rw [Presieve.map_ofArrows]
    apply zariskiPrecoverage_le_propQCPrecoverage
    exact (Scheme.Cover.mkOfCovers B.left (fun x ↦ (D x).left)
      (fun x ↦ (a x).left) hcover).mem₀
  let F := ((AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).sheafPushforwardContinuous
    (Type (u + 1)) (ProEt.topology S) (proEtaleModelTopology S)).obj
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.toSheaf (traceFieldRing l E S)).obj L))
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  apply (hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck hmem)).isSeparatedFor.ext
  intro Q g hg
  obtain ⟨x⟩ := hg
  change L.val.presheaf.map (AsSmall.up.map (a x)).op
      (∑ j, traceCoordinate l E p L σ₁ h₁ j s) =
    L.val.presheaf.map (AsSmall.up.map (a x)).op
      (∑ k, traceCoordinate l E p L σ₂ h₂ k s)
  simp only [map_sum]
  apply Fintype.sum_equiv (e x)
  intro j
  change L.val.map (AsSmall.up.map (a x)).op _ = L.val.map (AsSmall.up.map (a x)).op _
  rw [traceCoordinate_naturality, traceCoordinate_naturality]
  apply traceCoordinate_eq_of_sheet
  have hh := congrArg (fun q ↦ q ≫ pullback.snd B.hom p) (hsections x j)
  change ((W x).ι ≫ pullback.lift (𝟙 B.left) (h₁.left ≫ σ₁.sheet j) _) ≫
      pullback.snd B.hom p =
    ((W x).ι ≫ pullback.lift (𝟙 B.left) (h₂.left ≫ σ₂.sheet ((e x) j)) _) ≫
      pullback.snd B.hom p at hh
  simp only [Category.assoc, pullback.lift_snd] at hh
  change ((W x).ι ≫ h₁.left) ≫ σ₁.sheet j =
    ((W x).ι ≫ h₂.left) ≫ σ₂.sheet ((e x) j)
  simpa only [Category.assoc] using hh

private noncomputable def traceSourceSectionsColimit {X Y : Scheme.{u}} {f : Y ⟶ X} {T : X.Etale}
    (D : AlgebraicGeometry.Etale.FiniteEtaleTraceSplitting f T) :
    IsColimit (Cofan.mk (pullback T.hom f) (fun j ↦ D.t j ≫ D.i j)) := by
  refine Cofan.IsColimit.mk _ (fun c ↦ D.colimit.desc
    (Cofan.mk c.pt (fun j ↦ D.i j ≫ pullback.fst T.hom f ≫ c.inj j))) ?_ ?_
  · intro c j
    change (D.t j ≫ D.i j) ≫ _ = _
    have hh : D.i j ≫ D.colimit.desc
        (Cofan.mk c.pt (fun j ↦ D.i j ≫ pullback.fst T.hom f ≫ c.inj j)) =
        D.i j ≫ pullback.fst T.hom f ≫ c.inj j := D.colimit.fac _ ⟨j⟩
    rw [Category.assoc, hh]
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ c.inj j) (D.inv₁ j)
  · intro c m hm
    apply D.colimit.hom_ext
    intro ⟨j⟩
    change D.i j ≫ m = _
    rw [D.colimit.fac _ ⟨j⟩]
    calc
      _ = (D.i j ≫ pullback.fst T.hom f ≫ D.t j) ≫ D.i j ≫ m := by
        rw [D.inv₂, Category.id_comp]
      _ = D.i j ≫ pullback.fst T.hom f ≫ c.inj j := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ D.i j ≫ pullback.fst T.hom f ≫ k) (hm j)


private def traceSourceSplitting {T : S.Etale}
    (D : AlgebraicGeometry.Etale.FiniteEtaleTraceSplitting p T) :
    TraceImageSplitting p ((toProEt S).obj T) D.J := by
  let sheet (j : D.J) := D.t j ≫ D.i j ≫ pullback.snd T.hom p
  have hover (j : D.J) : sheet j ≫ p = T.hom := by
    dsimp only [sheet]
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun q ↦ q ≫ T.hom) (D.inv₁ j)
  have ha (j : D.J) : pullback.lift (𝟙 T.left) (sheet j)
      (by simpa only [Category.id_comp] using (hover j).symm) = D.t j ≫ D.i j := by
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst, Category.assoc] using (D.inv₁ j).symm
    · exact pullback.lift_snd _ _ _
  refine ⟨sheet, hover, ?_, ?_⟩
  · intro j
    have : IsIso (D.t j) := ⟨⟨D.i j ≫ pullback.fst T.hom p,
      D.inv₁ j, D.inv₂ j⟩⟩
    have := D.openImmersion j
    dsimp only [sheet]
    infer_instance
  · change IsColimit (Cofan.mk (pullback T.hom p) (fun j ↦
      pullback.lift (𝟙 T.left) (sheet j)
        (by simpa only [Category.id_comp] using (hover j).symm)))
    simp only [ha]
    exact traceSourceSectionsColimit D

private structure TraceSplitData (B : S.ProEt) where
  U : S.ProEt
  etale : Etale U.hom
  J : Type u
  finiteIndex : Fintype J
  splitting : TraceImageSplitting p U J
  map : B ⟶ U

private def traceSplitPresieve (B : S.ProEt) : Presieve B :=
  fun {C} _ ↦ Nonempty (TraceSplitData p C)

private theorem traceSplitPresieve_cover [IsFinite p] [Etale p] (B : S.ProEt) :
    Sieve.generate (traceSplitPresieve p B) ∈ ProEt.topology S B := by
  let W : S.Etale := MorphismProperty.Over.mk ⊤ (𝟙 S) inferInstance
  let R := Sieve.generate (AlgebraicGeometry.Etale.finiteEtaleTraceSplitPresieve p W)
  have hR : R ∈ S.smallEtaleTopology W :=
    AlgebraicGeometry.Etale.finiteEtaleTrace_split_cover p inferInstance inferInstance W
  have hν : CoverPreserving S.smallEtaleTopology (ProEt.topology S) (toProEt S) :=
    CategoryTheory.Functor.isContinuous_iff_coverPreserving.mp inferInstance
  let b : B ⟶ (toProEt S).obj W := MorphismProperty.Over.homMk B.hom (by simp [W])
  have hcov := (ProEt.topology S).pullback_stable b (hν.cover_preserve hR)
  apply (ProEt.topology S).superset_covering _ hcov
  intro C a ha
  obtain ⟨T, g, c, hg, _⟩ := ha
  obtain ⟨T', d, g', ⟨D⟩, _⟩ := hg
  apply Sieve.le_generate
  exact ⟨⟨(toProEt S).obj T', T'.prop, D.J, D.finiteIndex,
    traceSourceSplitting p D, c ≫ (toProEt S).map d⟩⟩

private def TraceSplitData.sum [Etale p] {B : S.ProEt} (D : TraceSplitData p B)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    L.val.obj (op (AsSmall.up.obj B)) :=
  letI := D.finiteIndex
  ∑ j, traceCoordinate l E p L D.splitting D.map j s

private def TraceSplitData.restrict {B C : S.ProEt} (D : TraceSplitData p B) (a : C ⟶ B) :
    TraceSplitData p C :=
  { D with map := a ≫ D.map }

private theorem traceSplitData_sum_eq [Etale p] {B : S.ProEt} (D D' : TraceSplitData p B)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    D.sum l E p L s = D'.sum l E p L s := by
  let := D.finiteIndex
  let := D'.finiteIndex
  exact traceCoordinate_sum_eq l E p L D.splitting D'.splitting D.map D'.map s

private theorem traceSplitData_sum_naturality [Etale p] {B C : S.ProEt}
    (D : TraceSplitData p B) (a : C ⟶ B)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    L.val.map (AsSmall.up.map a).op (D.sum l E p L s) =
      (D.restrict p a).sum l E p L
        (((traceModulePullback l E p).obj L).val.map
          (AsSmall.up.map ((proEtaleBaseChange p).map a)).op s) := by
  let := D.finiteIndex
  change L.val.presheaf.map (AsSmall.up.map a).op _ = _
  simp only [TraceSplitData.sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact traceCoordinate_naturality l E p L D.splitting D.map a j s

/-- A section over the finite cover has one descended sum, characterized after every
splitting and every restriction of its base.

Source: Stacks Project, sites.tex, Tag 04TQ; blueprint stratified-lattice proof,
"Pushing down by the trace" (blueprint: lem-sfb-finite-etale-trace-section-descent).

Proof. Use weakly-etale localization and the normalized continuous coefficient map
to identify module pullback with restriction on a sheet. The sheet unit is the
resulting isomorphism on sections. Finite etale local splitting gives an etale
cover of S, hence a pro-etale cover, including possibly empty sheet sets. Pull it
back to B and take the finite sum of the coordinates of the given section.
These sums commute with restrictions. On an overlap, the two decompositions differ
locally by a fixed permutation: intersect their clopen components and take the
finite intersections corresponding to bijections of their sheet sets. These loci
cover the overlap; if no bijection exists the overlap is empty. Reindexing the
finite sum and separatedness give agreement on overlaps. The sheaf axiom glues
the sums uniquely. Pulling the cover back to any other splitting proves the
stated formula there. Any two sections with these formulas agree on the original
cover, so are equal. The empty-cover axiom handles the empty base and empty sums. -/
theorem finiteEtaleTrace_section_sum_descent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {V S : Scheme.{u}} (p : V ⟶ S) [IsFinite p] [Etale p]
    (L : SheafOfModules.{u + 1} (traceFieldRing l E S))
    (B : S.ProEt)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    ∃! r : L.val.obj (op (AsSmall.up.obj B)),
      ∀ (U : S.ProEt) (_ : Etale U.hom) (J : Type u) [Fintype J]
        (σ : TraceImageSplitting p U J) (C : S.ProEt) (a : C ⟶ B) (h : C ⟶ U)
        (t : J → L.val.obj (op (AsSmall.up.obj C))),
        (∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
          (((traceModulePullback l E p).obj L).val.map
            (AsSmall.up.map ((proEtaleBaseChange p).map a)).op s) =
              traceImageSheetUnit l E p L σ h j (t j)) →
          L.val.map (AsSmall.up.map a).op r = ∑ j, t j := by
  classical
  let Q := (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L)
  let R := traceSplitPresieve p B
  let F := ((AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).sheafPushforwardContinuous
    (Type (u + 1)) (ProEt.topology S) (proEtaleModelTopology S)).obj
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.toSheaf (traceFieldRing l E S)).obj L))
  have hvalue (C : S.ProEt) (a : C ⟶ B) (ha : R a) :
      ∃! r : L.val.obj (op (AsSmall.up.obj C)),
        ∀ D : TraceSplitData p C,
          r = D.sum l E p L (Q.val.map (AsSmall.up.map a).op s) := by
    obtain ⟨D⟩ := ha
    refine ⟨D.sum l E p L (Q.val.map (AsSmall.up.map a).op s), ?_, ?_⟩
    · intro D'
      exact traceSplitData_sum_eq l E p L D D' _
    · intro r hr
      exact hr D
  let x : Presieve.FamilyOfElements F.obj R := fun {C} a ha ↦
    Classical.choose (hvalue C a ha).exists
  have hsum (C : S.ProEt) (a : C ⟶ B) (ha : R a) (D : TraceSplitData p C) :
      x a ha = D.sum l E p L (Q.val.map (AsSmall.up.map a).op s) :=
    Classical.choose_spec (hvalue C a ha).exists D
  have hx : x.Compatible := by
    intro C₁ C₂ Z g₁ g₂ a₁ a₂ ha₁ ha₂ he
    obtain ⟨D₁⟩ := ha₁
    obtain ⟨D₂⟩ := ha₂
    change L.val.map (AsSmall.up.map g₁).op (x a₁ ⟨D₁⟩) =
      L.val.map (AsSmall.up.map g₂).op (x a₂ ⟨D₂⟩)
    rw [hsum C₁ a₁ ⟨D₁⟩ D₁, hsum C₂ a₂ ⟨D₂⟩ D₂,
      traceSplitData_sum_naturality, traceSplitData_sum_naturality]
    have hcomp {C D : S.ProEt} (a : C ⟶ B) (g : D ⟶ C) :
        ((traceModulePullback l E p).obj L).val.map
            (AsSmall.up.map ((proEtaleBaseChange p).map g)).op
          (Q.val.map (AsSmall.up.map a).op s) =
        Q.val.map (AsSmall.up.map (g ≫ a)).op s := by
      change Q.val.presheaf.map (AsSmall.up.map g).op
        (Q.val.presheaf.map (AsSmall.up.map a).op s) = _
      rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
        ← op_comp, ← CategoryTheory.Functor.map_comp]
      rfl
    rw [hcomp, hcomp, he]
    exact traceSplitData_sum_eq l E p L (D₁.restrict p g₁) (D₂.restrict p g₂) _
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  obtain ⟨r, hr, huniq⟩ := hF.isSheafFor R (traceSplitPresieve_cover p B) x hx
  refine ⟨r, ?_, ?_⟩
  · intro U hU J inst σ C a h t ht
    let D : TraceSplitData p C := ⟨U, hU, J, inst, σ, h⟩
    change L.val.map (AsSmall.up.map a).op r = ∑ j, t j
    calc
      _ = D.sum l E p L (Q.val.map (AsSmall.up.map a).op s) :=
        (hr a ⟨D⟩).trans (hsum C a ⟨D⟩ D)
      _ = ∑ j, t j := by
        apply Finset.sum_congr rfl
        intro j _
        apply ((finiteEtaleTrace_sheet_lifting l E p L σ h).1 j).injective
        dsimp only
        rw [traceCoordinate_spec]
        exact ht j
  · intro r' hr'
    apply huniq r'
    intro C a ha
    obtain ⟨D⟩ := ha
    let := D.finiteIndex
    have hh := hr' D.U D.etale D.J D.splitting C a D.map
      (fun j ↦ traceCoordinate l E p L D.splitting D.map j
        (Q.val.map (AsSmall.up.map a).op s))
      (fun j ↦ (traceCoordinate_spec l E p L D.splitting D.map j _).symm)
    exact hh.trans (hsum C a ⟨D⟩ D).symm

end AlgebraicGeometry.Scheme
