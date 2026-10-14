/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Gluing

/-!
# The étale sheaf of sections of a descent cocycle

Let `f : V ⟶ Y` be weakly étale and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). The sections of the sheaf of sets defined by `c` over
étale `Y`-schemes (`AlgebraicGeometry.IsTwistedSection`) form a sheaf of sets on the small étale
site of `Y` (`AlgebraicGeometry.twistedSectionsPresheaf`,
`AlgebraicGeometry.isSheaf_twistedSectionsPresheaf`): sections glue along jointly surjective
étale families, the base changes of étale morphisms being open maps.

Twisted sections can be computed on any weakly étale `W ⟶ V` whose image covers the image of the
base (`AlgebraicGeometry.IsTwistedSection.bijective_restrict`): a section over a smaller cover
extends uniquely, by transport along the cocycle.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} {f : V ⟶ Y}

/-- The map `V ×_Y T' ⟶ V ×_Y T` induced by a morphism `t : T' ⟶ T` over `Y`. -/
noncomputable abbrev pullbackMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (f : V ⟶ Y) (t : T' ⟶ T) (ht : t ≫ π = π') : pullback f π' ⟶ pullback f π :=
  pullback.map f π' f π (𝟙 V) t (𝟙 Y) (by simp) (by simp [ht])

/-- Points of `V ×_Y T` lift along `V ×_Y T' ⟶ V ×_Y T` over any preimage in `T'` of their
image in `T`. -/
lemma exists_pullbackMapRight_eq {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (t : T' ⟶ T) (ht : t ≫ π = π') (x : ↥(pullback f π)) (t' : T')
    (h : t.base t' = (pullback.snd f π).base x) :
    ∃ x' : ↥(pullback f π'), (pullbackMapRight f t ht).base x' = x ∧
      (pullback.snd f π').base x' = t' := by
  obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f π)
    (g := t) x t' h.symm
  let L : pullback (pullback.snd f π) t ⟶ pullback f π' :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, ← ht, pullback.condition_assoc])
  have hL₁ : L ≫ pullbackMapRight f t ht = pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp [L]
    · simp [L, pullback.condition]
  have hL₂ : L ≫ pullback.snd f π' = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine ⟨L.base y, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hL₁, hy₁]
  · rw [← Scheme.Hom.comp_apply, hL₂, hy₂]

@[simp]
lemma pullbackMapRight_fst {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pullbackMapRight f t ht ≫ pullback.fst f π = pullback.fst f π' := by
  simp [pullbackMapRight]

@[simp]
lemma pullbackMapRight_snd {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pullbackMapRight f t ht ≫ pullback.snd f π = pullback.snd f π' ≫ t := by
  simp [pullbackMapRight]

lemma pullbackMapRight_id {T : Scheme.{u}} (π : T ⟶ Y) (h : 𝟙 T ≫ π = π) :
    pullbackMapRight f (𝟙 T) h = 𝟙 _ :=
  pullback.hom_ext (by simp) (by simp)

lemma pullbackMapRight_comp {T T' T'' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    {π'' : T'' ⟶ Y} (t : T' ⟶ T) (ht : t ≫ π = π') (t' : T'' ⟶ T') (ht' : t' ≫ π' = π'')
    (h : (t' ≫ t) ≫ π = π'') :
    pullbackMapRight f (t' ≫ t) h = pullbackMapRight f t' ht' ≫ pullbackMapRight f t ht :=
  pullback.hom_ext (by simp) (by simp)

/-- The map `R_{T'} ⟶ R_T` of the schemes of pairs `R_T = (V ×_Y T) ×_T (V ×_Y T)` induced by a
morphism `t : T' ⟶ T` over `Y`. -/
noncomputable abbrev pairMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (f : V ⟶ Y) (t : T' ⟶ T) (ht : t ≫ π = π') :
    pullback (pullback.snd f π') (pullback.snd f π') ⟶
      pullback (pullback.snd f π) (pullback.snd f π) :=
  pullback.map _ _ _ _ (pullbackMapRight f t ht) (pullbackMapRight f t ht) t (by simp)
    (by simp)

lemma pairMapRight_fst {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pairMapRight f t ht ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullbackMapRight f t ht := by
  simp [pairMapRight]

lemma pairMapRight_snd {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pairMapRight f t ht ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullbackMapRight f t ht := by
  simp [pairMapRight]

lemma pairMapRight_twistedPairMap {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pairMapRight f t ht ≫ twistedPairMap f π = twistedPairMap f π' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [reassoc_of% pairMapRight_fst]
    simp
  · simp only [Category.assoc, pullback.lift_snd]
    rw [reassoc_of% pairMapRight_snd]
    simp

/-- Points of `R_T` lift along `R_{T'} ⟶ R_T` over any preimage in `T'` of their image in
`T`. -/
lemma exists_pairMapRight_eq {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (t : T' ⟶ T) (ht : t ≫ π = π') (w : ↥(pullback (pullback.snd f π) (pullback.snd f π)))
    (t' : T') (h : t.base t' =
      (pullback.fst (pullback.snd f π) (pullback.snd f π) ≫ pullback.snd f π).base w) :
    ∃ w' : ↥(pullback (pullback.snd f π') (pullback.snd f π')),
      (pairMapRight f t ht).base w' = w := by
  set τ := pullback.fst (pullback.snd f π) (pullback.snd f π) ≫ pullback.snd f π
  obtain ⟨y, hy₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := τ) (g := t) w t' h.symm
  have e : pullback.fst τ t ≫ τ = pullback.snd τ t ≫ t := pullback.condition
  have h₁ : (pullback.fst τ t ≫ pullback.fst (pullback.snd f π) (pullback.snd f π) ≫
      pullback.fst f π) ≫ f = pullback.snd τ t ≫ π' := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := f) (g := π), ← ht,
      ← Category.assoc (pullback.snd τ t), ← e]
    simp [τ]
  have h₂ : (pullback.fst τ t ≫ pullback.snd (pullback.snd f π) (pullback.snd f π) ≫
      pullback.fst f π) ≫ f = pullback.snd τ t ≫ π' := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := f) (g := π),
      ← pullback.condition_assoc (f := pullback.snd f π) (g := pullback.snd f π), ← ht,
      ← Category.assoc (pullback.snd τ t), ← e]
    simp [τ]
  let L : pullback τ t ⟶ pullback (pullback.snd f π') (pullback.snd f π') :=
    pullback.lift (pullback.lift _ _ h₁) (pullback.lift _ _ h₂) (by simp)
  have hL : L ≫ pairMapRight f t ht = pullback.fst τ t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pairMapRight_fst]
      apply pullback.hom_ext
      · simp [L]
      · simp only [L, Category.assoc, pullbackMapRight_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
        rw [← pullback.condition (f := τ) (g := t)]
    · rw [Category.assoc, pairMapRight_snd]
      apply pullback.hom_ext
      · simp [L]
      · simp only [L, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
        rw [← pullback.condition (f := τ) (g := t)]
        simp only [τ, pullback.condition]
  exact ⟨L.base y, by rw [← Scheme.Hom.comp_apply, hL, hy₁]⟩

variable (f) in
/-- The presheaf of sections of the sheaf of sets defined by a descent cocycle `c`, on the
small étale site of `Y`. -/
noncomputable def twistedSectionsPresheaf {S : Type u} (c : ↥(pullback f f) → S → S) :
    Y.Etaleᵒᵖ ⥤ Type u where
  obj U := {σ : ↥(pullback f U.unop.hom) → S // IsTwistedSection f c U.unop.hom σ}
  map {U U'} g := ↾fun σ ↦
    ⟨σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base,
      σ.2.comp g.unop.left (MorphismProperty.Over.w g.unop)⟩
  map_id U := by
    ext σ : 3
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) _).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 3
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (g'.unop.left ≫ g.unop.left) _).base =
      (σ.1 ∘ (pullbackMapRight f g.unop.left _).base) ∘ (pullbackMapRight f g'.unop.left _).base
    rw [pullbackMapRight_comp g.unop.left (MorphismProperty.Over.w g.unop) g'.unop.left
      (MorphismProperty.Over.w g'.unop)]
    rfl

lemma twistedSectionsPresheaf_map_coe {S : Type u} (c : ↥(pullback f f) → S → S)
    {U U' : Y.Etale} (g : U' ⟶ U) (σ : (twistedSectionsPresheaf f c).obj (op U)) :
    ((twistedSectionsPresheaf f c).map g.op σ).1 =
      σ.1 ∘ (pullbackMapRight f g.left (MorphismProperty.Over.w g)).base :=
  rfl

/-- The square of `V ×_Y T' ⟶ V ×_Y T` over `t : T' ⟶ T` is cartesian. -/
lemma isPullback_pullbackMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') :
    IsPullback (pullbackMapRight f t ht) (pullback.snd f π') (pullback.snd f π) t := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f π) (v₁₃ := f) (h₂₂ := π) ?_ (by simp)
    (IsPullback.of_hasPullback f π)
  rw [pullbackMapRight_fst, ht]
  exact IsPullback.of_hasPullback f π'

instance {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T) [Etale t]
    (ht : t ≫ π = π') : Etale (pullbackMapRight f t ht) :=
  MorphismProperty.of_isPullback (isPullback_pullbackMapRight t ht).flip ‹_›

/-- The morphisms of the small étale site are étale. -/
lemma etale_left {U U' : Y.Etale} (g : U' ⟶ U) : Etale g.left := by
  have : Etale (g.left ≫ U.hom) := by rw [MorphismProperty.Over.w g]; exact U'.prop
  exact Etale.of_comp g.left U.hom

variable (f) in
/-- **Twisted sections glue along jointly surjective étale families.** -/
lemma isSheafFor_ofArrows_twistedSectionsPresheaf {S : Type u} (c : ↥(pullback f f) → S → S)
    {U : Y.Etale} {ι : Type*} (Ui : ι → Y.Etale) (π : ∀ i, Ui i ⟶ U)
    (hsurj : ∀ u : U.left, ∃ i, ∃ x, (π i).left.base x = u) :
    (Presieve.ofArrows Ui π).IsSheafFor (twistedSectionsPresheaf f c) := by
  classical
  have := fun i ↦ etale_left (π i)
  let M (i : ι) := pullbackMapRight f (π i).left (MorphismProperty.Over.w (π i))
  have hMs (i : ι) : M i ≫ pullback.snd f U.hom = pullback.snd f (Ui i).hom ≫ (π i).left :=
    pullbackMapRight_snd _ _
  have hMf (i : ι) : M i ≫ pullback.fst f U.hom = pullback.fst f (Ui i).hom :=
    pullbackMapRight_fst _ _
  have hM (p : ↥(pullback f U.hom)) : ∃ i, ∃ q, (M i).base q = p := by
    obtain ⟨i, u, hu⟩ := hsurj ((pullback.snd f U.hom).base p)
    obtain ⟨q, hq, -⟩ := exists_pullbackMapRight_eq (f := f) (π i).left
      (MorphismProperty.Over.w (π i)) p u hu
    exact ⟨i, q, hq⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- compatibility at points
  have hcompat (i j : ι) (q : ↥(pullback f (Ui i).hom)) (q' : ↥(pullback f (Ui j).hom))
      (h : (M i).base q = (M j).base q') : (x i).1 q = (x j).1 q' := by
    have : Etale (pullback.fst (π i).left (π j).left ≫ (Ui i).hom) := by
      have := etale_left (π j)
      infer_instance
    let Z : Y.Etale := Scheme.Etale.mk (pullback.fst (π i).left (π j).left ≫ (Ui i).hom)
    let g₁ : Z ⟶ Ui i := MorphismProperty.Over.homMk (pullback.fst _ _) rfl trivial
    let g₂ : Z ⟶ Ui j := MorphismProperty.Over.homMk (pullback.snd _ _) (by
      change pullback.snd _ _ ≫ (Ui j).hom = pullback.fst _ _ ≫ (Ui i).hom
      rw [← MorphismProperty.Over.w (π i), ← MorphismProperty.Over.w (π j),
        pullback.condition_assoc]) trivial
    have hg : g₁ ≫ π i = g₂ ≫ π j :=
      MorphismProperty.Over.Hom.ext pullback.condition
    have e := congrArg Subtype.val (hx i j Z g₁ g₂ hg)
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := M i) (g := M j) q q' h
    have hc : (pullback.fst (M i) (M j) ≫ pullback.snd f (Ui i).hom) ≫ (π i).left =
        (pullback.snd (M i) (M j) ≫ pullback.snd f (Ui j).hom) ≫ (π j).left := by
      rw [Category.assoc, Category.assoc, ← hMs, ← hMs]
      exact pullback.condition_assoc _
    let L : pullback (M i) (M j) ⟶ pullback f Z.hom :=
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.lift _ _ hc) (by
        change _ = _ ≫ pullback.fst _ _ ≫ (Ui i).hom
        simp [pullback.condition])
    have hL₁ : L ≫ pullbackMapRight f g₁.left (MorphismProperty.Over.w g₁) =
        pullback.fst (M i) (M j) := pullback.hom_ext (by simp [L]) (by simp [L, g₁])
    have hL₂ : L ≫ pullbackMapRight f g₂.left (MorphismProperty.Over.w g₂) =
        pullback.snd (M i) (M j) := by
      apply pullback.hom_ext
      · have := pullback.condition_assoc (f := M i) (g := M j) (pullback.fst f U.hom)
        rw [hMf, hMf] at this
        rw [Category.assoc, pullbackMapRight_fst]
        exact (pullback.lift_fst _ _ _).trans this
      · simp [L, g₂]
    have e' := congrFun e (L.base y)
    simp only [twistedSectionsPresheaf_map_coe, Function.comp_apply] at e'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hL₁, hL₂, hy₁, hy₂] at e'
    exact e'
  choose ii qq hqq using hM
  let σ : ↥(pullback f U.hom) → S := fun p ↦ (x (ii p)).1 (qq p)
  have hσM (i : ι) (q : ↥(pullback f (Ui i).hom)) : σ ((M i).base q) = (x i).1 q :=
    hcompat _ _ _ _ (hqq _)
  have hσ : IsTwistedSection f c U.hom σ := by
    refine ⟨?_, fun w ↦ ?_⟩
    · refine IsLocallyConstant.iff_isOpen_fiber.2 fun a ↦ ?_
      have : σ ⁻¹' {a} = ⋃ i, (M i).base '' ((x i).1 ⁻¹' {a}) := by
        ext p
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image]
        refine ⟨fun hp ↦ ⟨ii p, qq p, hp, hqq p⟩, ?_⟩
        rintro ⟨i, q, hq, rfl⟩
        rw [hσM, hq]
      rw [this]
      exact isOpen_iUnion fun i ↦ (M i).isOpenMap _ ((x i).2.1.isOpen_fiber a)
    · obtain ⟨i, u, hu⟩ := hsurj
        ((pullback.fst (pullback.snd f U.hom) (pullback.snd f U.hom) ≫ pullback.snd f U.hom).base
          w)
      obtain ⟨w', hw'⟩ := exists_pairMapRight_eq (f := f) (π i).left
        (MorphismProperty.Over.w (π i)) w u hu
      have h₁ := congrArg (fun φ ↦ φ.base w') (pairMapRight_fst (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      have h₂ := congrArg (fun φ ↦ φ.base w') (pairMapRight_snd (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      have h₃ := congrArg (fun φ ↦ φ.base w') (pairMapRight_twistedPairMap (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      simp only [Scheme.Hom.comp_apply, hw'] at h₁ h₂ h₃
      rw [h₁, h₂, h₃, hσM, hσM]
      exact (x i).2.2 w'
  refine ⟨⟨σ, hσ⟩, fun i ↦ Subtype.ext (funext fun q ↦ hσM i q), fun t ht ↦ ?_⟩
  refine Subtype.ext (funext fun p ↦ ?_)
  obtain ⟨i, q, rfl⟩ : ∃ i q, (M i).base q = p := ⟨ii p, qq p, hqq p⟩
  have := congrFun (congrArg Subtype.val (ht i)) q
  simp only [twistedSectionsPresheaf_map_coe, Function.comp_apply] at this
  change t.1 ((M i).base q) = σ ((M i).base q)
  rw [this, hσM]

variable (f) in
/-- **The sections of a descent cocycle form a sheaf on the small étale site.** -/
theorem isSheaf_twistedSectionsPresheaf {S : Type u} (c : ↥(pullback f f) → S → S) :
    Presheaf.IsSheaf Y.smallEtaleTopology (twistedSectionsPresheaf f c) := by
  rw [isSheaf_iff_isSheaf_of_type, Scheme.smallEtaleTopology,
    Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Presieve.isSheaf_pretopology]
  rintro U _ ⟨𝒰, _, h, rfl⟩
  refine isSheafFor_ofArrows_twistedSectionsPresheaf f c _ _ fun u ↦ ?_
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq u
  exact ⟨i, x, hx⟩

end AlgebraicGeometry
