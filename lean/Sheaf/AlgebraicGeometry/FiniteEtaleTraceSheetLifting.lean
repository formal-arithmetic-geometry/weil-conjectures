/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.Scheme

/-! # Sheet coordinates and gluing integral sheet sections -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace ProEt

/-- The empty covering forces a sheaf to have exactly one section on an empty object. -/
private theorem sections_unique_of_isEmpty {X : Scheme.{u}} (T : X.ProEt)
    [IsEmpty T.left] (F : Sheaf (topology X) (Type (u + 1))) :
    Nonempty (Unique (F.obj.obj (op T))) := by
  exact ⟨Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover T (bot_mem_topology T))⟩

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Sections on a finite disjoint union are the product of the sections on its summands.

Source: Stacks Project, Tag 0F4P, proof of `lemma-weakly-contractible-cover`, and
Tag 0DB1, hypotheses (a)--(c) of `remark-take-unions-hypercovering-X`.
The proof uses the sheaf equalizer condition for the finite pro-etale covering by the
pairwise disjoint open summands: off-diagonal pullbacks are empty and diagonal pullbacks
are identities, so compatible tuples glue uniquely. The empty family is included; its
cover is the empty cover and the sheaf axiom gives a singleton of sections.
Adapted from `ProEt.finite_coproduct_sheaf_core`, whose qcqs hypotheses
are unused in the proof; no compactness assumption is needed here.
-/
private theorem traceFiniteCoproductSections (X : Scheme.{u}) (I : Type u) [Finite I]
    (V : I → X.ProEt) (W : X.ProEt) (ι : ∀ i, V i ⟶ W)
    (e : (∐ fun i ↦ (V i).left) ≅ W.left)
    (hι : ∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left) :
    (∀ F : Sheaf (topology X) (Type (u + 1)),
        Function.Bijective (fun s : F.obj.obj (op W) ↦
          fun i ↦ F.obj.map (ι i).op s)) ∧
      (IsEmpty I → IsEmpty W.left ∧
        ∀ F : Sheaf (topology X) (Type (u + 1)),
          Nonempty (Unique (F.obj.obj (op W)))) := by
  classical
  have hopen (i : I) : IsOpenImmersion (ι i).left := by
    rw [← hι i]
    infer_instance
  have hcover : ∀ x : W.left, ∃ i y, (ι i).left y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun i ↦ (V i).left)).exists_eq (e.inv x)
    change (Sigma.ι (fun i ↦ (V i).left) i) y = e.inv x at hy
    refine ⟨i, y, ?_⟩
    rw [← hι i, Hom.comp_apply, hy]
    simp [← Hom.comp_apply]
  have hmem : Presieve.ofArrows V ι ∈ precoverage X W := by
    change (Presieve.ofArrows V ι).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    apply zariskiPrecoverage_le_propQCPrecoverage
    exact (Scheme.Cover.mkOfCovers I (fun i ↦ (V i).left)
      (fun i ↦ (ι i).left) hcover).mem₀
  have hsieve : Sieve.ofArrows V ι ∈ topology X W :=
    Precoverage.generate_mem_toGrothendieck hmem
  have hbij (F : Sheaf (topology X) (Type (u + 1))) :
      Function.Bijective (fun s : F.obj.obj (op W) ↦
        fun i ↦ F.obj.map (ι i).op s) := by
    have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
    have hglue := (Presieve.isSheafFor_arrows_iff F.obj ι).mp
      (hF.isSheafFor _ hsieve)
    have hcompat (s : ∀ i, F.obj.obj (op (V i))) :
        Presieve.Arrows.Compatible F.obj ι s := by
      intro i j T a b hab
      by_cases hij : i = j
      · subst j
        have hab' : a.left = b.left := by
          apply (cancel_mono (ι i).left).mp
          exact congrArg (fun f ↦ f.left) hab
        have : a = b := MorphismProperty.Over.Hom.ext hab'
        subst b
        rfl
      · have hempty : IsEmpty T.left := by
          apply isEmpty_of_commSq_sigmaι_of_ne
            (g := fun i ↦ (V i).left) (a := a.left) (b := b.left) _ hij
          constructor
          apply (cancel_mono e.hom).mp
          rw [Category.assoc, Category.assoc, hι, hι]
          exact congrArg (fun f ↦ f.left) hab
        obtain ⟨hunique⟩ := sections_unique_of_isEmpty T F
        exact hunique.uniq _ |>.trans (hunique.uniq _).symm
    constructor
    · intro s t hst
      exact (hglue _ (hcompat _)).unique (fun i ↦ rfl) (fun i ↦ congrFun hst.symm i)
    · intro s
      obtain ⟨t, ht, _⟩ := hglue s (hcompat s)
      exact ⟨t, funext ht⟩
  constructor
  · exact hbij
  · intro hI
    let _ : IsEmpty I := hI
    have hempty : IsEmpty W.left := ⟨fun x ↦ by
      obtain ⟨i, _, _⟩ := hcover x
      exact isEmptyElim i⟩
    exact ⟨hempty, fun F ↦ sections_unique_of_isEmpty W F⟩


end ProEt

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V S : Scheme.{u}} (p : V ⟶ S)
  (L : SheafOfModules.{u + 1} (traceFieldRing l E S))

private def traceRestrictionSite [Etale p] :
    proEtaleSiteModel V ⥤ proEtaleSiteModel S :=
  AsSmall.down ⋙ MorphismProperty.Over.map (f := p) ⊤ inferInstance ⋙ AsSmall.up

private def traceRestrictionSiteAdj [Etale p] :
    traceRestrictionSite p ⊣ proEtaleModelBaseChange p :=
  ((AsSmall.equiv.{u, u + 1, u + 1} (C := V.ProEt)).symm.toAdjunction.comp
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ p inferInstance trivial)).comp
      (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).toAdjunction

private instance traceRestrictionSite_continuous [Etale p] :
    (traceRestrictionSite p).IsContinuous (proEtaleModelTopology V)
      (proEtaleModelTopology S) := by
  have : (MorphismProperty.Over.map (f := p) ⊤ (show WeaklyEtale p from inferInstance)).IsContinuous
      (ProEt.topology V) (ProEt.topology S) := ProEt.isContinuous_overMap inferInstance
  have : (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).IsContinuous
      (ProEt.topology S) (proEtaleModelTopology S) := proEtaleModelUp_isContinuous S
  have := CategoryTheory.Functor.isContinuous_comp
    (MorphismProperty.Over.map (f := p) ⊤ (show WeaklyEtale p from inferInstance))
    (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S)
    (ProEt.topology V) (ProEt.topology S) (proEtaleModelTopology S)
  exact CategoryTheory.Functor.isContinuous_comp
    (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt)
    (MorphismProperty.Over.map (f := p) ⊤ (show WeaklyEtale p from inferInstance) ⋙ AsSmall.up)
    (proEtaleModelTopology V) (ProEt.topology V) (proEtaleModelTopology S)

private def traceRestrictionRingMap [Etale p] :
    traceFieldRing l E V ⟶
      ((traceRestrictionSite p).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology V) (proEtaleModelTopology S)).obj (traceFieldRing l E S) :=
  ⟨{ app X := 𝟙 _
     naturality := by
       intro X Y f
       simp only [Category.id_comp, Category.comp_id]
       rfl }⟩

private theorem traceRestrictionRing_counit [Etale p] :
    CategoryTheory.Functor.whiskerRight
        (NatTrans.op (traceRestrictionSiteAdj p).counit) (traceFieldRing l E S).obj =
      (traceFieldRingMap l E p).hom ≫ (proEtaleModelBaseChange p).op.whiskerLeft
        (traceRestrictionRingMap l E p).hom := by
  ext X s
  rfl

set_option linter.flexible false in
private theorem traceRestrictionRing_unit [Etale p] :
    (traceRestrictionRingMap l E p).hom ≫ (traceRestrictionSite p).op.whiskerLeft
        (traceFieldRingMap l E p).hom ≫
      CategoryTheory.Functor.whiskerRight
        (NatTrans.op (traceRestrictionSiteAdj p).unit) (traceFieldRing l E V).obj =
      𝟙 _ := by
  let := coefficientExtensionNormedField l E
  ext X s
  change C((AsSmall.down.obj X.unop).left, ULift.{u + 1, u} E) at s
  apply ContinuousMap.ext
  intro x
  change s _ = s _
  congr 1
  have hh : (pullback.fst ((AsSmall.down.obj X.unop).hom ≫ p) p)
      ((pullback.lift (𝟙 _) (AsSmall.down.obj X.unop).hom (by simp)) x) = x := by
    rw [← Hom.comp_apply, pullback.lift_fst]
    rfl
  simp [traceRestrictionSiteAdj, Adjunction.comp_unit_app,
    MorphismProperty.Over.mapPullbackAdj, AsSmall.equiv, traceRestrictionSite]
  exact hh

private def tracePullbackRestrictionIso [Etale p] :
    traceModulePullback l E p ≅ SheafOfModules.pushforward (traceRestrictionRingMap l E p) :=
  (SheafOfModules.pullbackPushforwardAdjunction (traceFieldRingMap l E p)).leftAdjointUniq
    (SheafOfModules.pushforwardPushforwardAdj (traceRestrictionSiteAdj p)
      (traceRestrictionRingMap l E p) (traceFieldRingMap l E p)
      (traceRestrictionRing_counit l E p) (traceRestrictionRing_unit l E p))

private theorem tracePullbackRestrictionIso_unit [Etale p] (B : S.ProEt)
    (s : L.val.obj (op (AsSmall.up.obj B))) :
    ((tracePullbackRestrictionIso l E p).hom.app L).val.app
        (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))
      ((((SheafOfModules.pullbackPushforwardAdjunction
        (traceFieldRingMap l E p)).unit.app L).val.app (op (AsSmall.up.obj B))) s) =
      L.val.map ((traceRestrictionSiteAdj p).counit.app (AsSmall.up.obj B)).op s := by
  have hh := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction (traceFieldRingMap l E p))
    (SheafOfModules.pushforwardPushforwardAdj (traceRestrictionSiteAdj p)
      (traceRestrictionRingMap l E p) (traceFieldRingMap l E p)
      (traceRestrictionRing_counit l E p) (traceRestrictionRing_unit l E p)) L
  exact congrArg (fun k ↦ k.val.app (op (AsSmall.up.obj B)) s) hh

private def traceSheetBaseIso [Etale p] {U : S.ProEt} {J : Type u}
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J) :
    (traceRestrictionSite p).obj (AsSmall.up.obj (traceImageSheetObject σ h j)) ≅
      AsSmall.up.obj B :=
  AsSmall.up.mapIso (MorphismProperty.Over.isoMk (Iso.refl B.left) (by
    change 𝟙 B.left ≫ B.hom = (h.left ≫ σ.sheet j) ≫ p
    simp [Category.assoc, σ.over]))

private theorem traceSheetComparison_unit [Etale p] {U : S.ProEt} {J : Type u}
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J)
    (s : L.val.obj (op (AsSmall.up.obj B))) :
    ((tracePullbackRestrictionIso l E p).hom.app L).val.app
        (op (AsSmall.up.obj (traceImageSheetObject σ h j)))
      (traceImageSheetUnit l E p L σ h j s) =
        L.val.map (traceSheetBaseIso p σ h j).hom.op s := by
  let η := ((SheafOfModules.pullbackPushforwardAdjunction
    (traceFieldRingMap l E p)).unit.app L).val.app (op (AsSmall.up.obj B))
  have hn := PresheafOfModules.naturality_apply
    ((tracePullbackRestrictionIso l E p).hom.app L).val
    (AsSmall.up.map (traceImageSheetArrow σ h j)).op (η s)
  unfold traceImageSheetUnit traceImageSheetRestriction
  erw [hn]
  rw [tracePullbackRestrictionIso_unit]
  change L.val.map ((traceRestrictionSite p).map
    (AsSmall.up.map (traceImageSheetArrow σ h j))).op
      (L.val.map ((traceRestrictionSiteAdj p).counit.app (AsSmall.up.obj B)).op s) = _
  erw [← PresheafOfModules.map_comp_apply, ← op_comp]
  have he : (traceRestrictionSite p).map (AsSmall.up.map (traceImageSheetArrow σ h j)) ≫
      (traceRestrictionSiteAdj p).counit.app (AsSmall.up.obj B) =
        (traceSheetBaseIso p σ h j).hom := by
    apply (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse.map_injective
    apply MorphismProperty.Over.Hom.ext
    simp only [AsSmall.equiv_inverse, AsSmall.down_obj, CategoryTheory.Functor.id_obj,
      AsSmall.up_obj_down, AsSmall.down_map]
    exact pullback.lift_fst _ _ _
  rw [he]
  rfl

private theorem traceSheetUnit_bijective [Etale p] {U : S.ProEt} {J : Type u}
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J) :
    Function.Bijective (fun t : L.val.obj (op (AsSmall.up.obj B)) ↦
      traceImageSheetUnit l E p L σ h j t) := by
  let i := (tracePullbackRestrictionIso l E p).app L
  let X := op (AsSmall.up.obj (traceImageSheetObject σ h j))
  have hi : Function.Bijective (fun x ↦ i.hom.val.app X x) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hh := congrArg (fun z ↦ i.inv.val.app X z) hxy
      change ((i.hom ≫ i.inv).val.app X) x = ((i.hom ≫ i.inv).val.app X) y at hh
      rw [i.hom_inv_id] at hh
      exact hh
    · intro y
      refine ⟨i.inv.val.app X y, ?_⟩
      change ((i.inv ≫ i.hom).val.app X) y = y
      rw [i.inv_hom_id]
      rfl
  have hb : Function.Bijective (fun s ↦ L.val.map (traceSheetBaseIso p σ h j).hom.op s) := by
    change Function.Bijective (L.val.presheaf.map (traceSheetBaseIso p σ h j).hom.op)
    exact ConcreteCategory.bijective_of_isIso _
  have he : (fun x ↦ i.hom.val.app X x) ∘
      (fun t ↦ traceImageSheetUnit l E p L σ h j t) =
      (fun s ↦ L.val.map (traceSheetBaseIso p σ h j).hom.op s) := by
    funext s
    exact traceSheetComparison_unit l E p L σ h j s
  rw [← he] at hb
  constructor
  · intro x y hxy
    apply hb.injective
    simp only [Function.comp_apply, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (i.hom.val.app X y)
    exact ⟨x, hi.injective hx⟩

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

private theorem traceSheetIntegralGlue {U : S.ProEt} {J : Type u} [Finite J]
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U)
    (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
      ((traceModulePullback l E p).obj L)).val.Submodule)
    (hM : Presheaf.IsSheaf (proEtaleModelTopology V) M.toPresheafOfModules.presheaf)
    (t : J → L.val.obj (op (AsSmall.up.obj B)))
    (ht : ∀ j, traceImageSheetUnit l E p L σ h j (t j) ∈
      M.obj (op (AsSmall.up.obj (traceImageSheetObject σ h j)))) :
    ∃ m : M.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B))),
      ∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L) m.val =
        traceImageSheetUnit l E p L σ h j (t j) := by
  let := Fintype.ofFinite J
  let W := (proEtaleBaseChange p).obj B
  let D (j : J) := traceImageSheetObject σ h j
  let a (j : J) : D j ⟶ W := traceImageSheetArrow σ h j
  let hc := traceSheetCoproduct p σ h
  let e := (coproductIsCoproduct (fun j ↦ (D j).left)).coconePointUniqueUpToIso hc
  have he (j : J) : Sigma.ι (fun j ↦ (D j).left) j ≫ e.hom = (a j).left := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk j)
  let F₀ : Sheaf (proEtaleModelTopology V) AddCommGrpCat.{u + 1} :=
    ⟨M.toPresheafOfModules.presheaf, hM⟩
  let F := ((AsSmall.up : V.ProEt ⥤ proEtaleSiteModel V).sheafPushforwardContinuous
    (Type (u + 1)) (ProEt.topology V) (proEtaleModelTopology V)).obj
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F₀)
  obtain ⟨m, hm⟩ := (ProEt.traceFiniteCoproductSections V J D W a e he).1 F |>.surjective
    (fun j ↦ (⟨_, ht j⟩ : M.obj (op (AsSmall.up.obj (D j)))))
  refine ⟨m, ?_⟩
  intro j
  exact congrArg Subtype.val (congrFun hm j)

/-- On a finite splitting, every rational section has sheet coordinates, and any
integral tuple in those coordinates glues to an integral section on the cover.

Source: Stacks Project, sites.tex, Tags 03CE and 00VM; blueprint stratified-lattice
proof, "Pushing down by the trace"
(blueprint: lem-sfb-finite-etale-trace-sheet-lifting).

Proof. Localization identifies pullback along a pro-etale object with restriction.
Under this identification the canonical continuous coefficient map is identity:
its adjunct restricts a function along the fibre-product projection, whose
composite with the distinguished sheet section is identity. The module unit on
each sheet is therefore an isomorphism. Its inverse sends restrictions of any
rational section to the asserted coordinates. Pull the coproduct splitting back
from U to B. Its sheet inclusions are pairwise disjoint clopen immersions and cover
the fibre product. A tuple of sections of M is matching: diagonal overlaps impose
identity and off-diagonal overlaps are empty, where module sections are zero.
The sheaf axiom for M glues this tuple to m. The same argument works for empty
sheet sets, giving the zero section on the empty fibre product. -/
theorem finiteEtaleTrace_sheet_lifting
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {V S : Scheme.{u}} (p : V ⟶ S) [Etale p]
    (L : SheafOfModules.{u + 1} (traceFieldRing l E S))
    {U : S.ProEt} {J : Type u} [Finite J] (σ : TraceImageSplitting p U J)
    {B : S.ProEt} (h : B ⟶ U) :
    (∀ j, Function.Bijective (fun t : L.val.obj (op (AsSmall.up.obj B)) ↦
      traceImageSheetUnit l E p L σ h j t)) ∧
    ∀ (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
        ((traceModulePullback l E p).obj L)).val.Submodule)
      (_ : Presheaf.IsSheaf (proEtaleModelTopology V) M.toPresheafOfModules.presheaf)
      (t : J → L.val.obj (op (AsSmall.up.obj B))),
      (∀ j, traceImageSheetUnit l E p L σ h j (t j) ∈
        M.obj (op (AsSmall.up.obj (traceImageSheetObject σ h j)))) →
      ∃ m : M.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B))),
        ∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L) m.val =
          traceImageSheetUnit l E p L σ h j (t j) := by
  exact ⟨traceSheetUnit_bijective l E p L σ h,
    traceSheetIntegralGlue l E p L σ h⟩

end AlgebraicGeometry.Scheme
