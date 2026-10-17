/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Etale

/-!
# Quasi-compact quasi-separated objects of the small étale site

We call an object `Y` of `X.Etale` *qcqs* if its structure morphism `Y ⟶ X` is quasi-compact
and quasi-separated. Such objects are closed under finite limits and finite coproducts.
We also show that a covering sieve of a quasi-compact étale `X`-scheme contains a finite
jointly surjective family of affine étale schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/-- Let `Z` be covered by finitely many open embeddings with pairwise disjoint ranges. Then a
subset of `Z` is quasi-separated as soon as all its preimages are. -/
lemma IsQuasiSeparated.of_isOpenEmbedding_cover {Z : Type*} [TopologicalSpace Z]
    {ι : Type*} [Finite ι] {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (j : ∀ i, Y i → Z)
    (hj : ∀ i, Topology.IsOpenEmbedding (j i))
    (hdisj : Pairwise fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k)))
    (hcov : ∀ z, ∃ i y, j i y = z) {s : Set Z} (hs : ∀ i, IsQuasiSeparated (j i ⁻¹' s)) :
    IsQuasiSeparated s := by
  have hclosed (i : ι) : IsClosed (Set.range (j i)) := by
    have hc : (Set.range (j i))ᶜ = ⋃ (k : ι) (_ : k ≠ i), Set.range (j k) := by
      ext z
      obtain ⟨k, y, rfl⟩ := hcov z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_range, exists_prop]
      constructor
      · intro hz
        refine ⟨k, ?_, y, rfl⟩
        rintro rfl
        exact hz ⟨y, rfl⟩
      · rintro ⟨l, hli, y', hy'⟩ ⟨y'', hy''⟩
        exact Set.disjoint_left.mp (hdisj hli) ⟨y', hy'⟩ ⟨y'', hy''⟩
    rw [← isOpen_compl_iff, hc]
    exact isOpen_biUnion fun k _ ↦ (hj k).isOpen_range
  intro U V hUs hUo hUc hVs hVo hVc
  have hUV : U ∩ V = ⋃ i, j i '' (j i ⁻¹' U ∩ j i ⁻¹' V) := by
    ext z
    obtain ⟨i, y, rfl⟩ := hcov z
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨i, y, h, rfl⟩
    · rintro ⟨k, y', h, hy'⟩
      rw [← hy']
      exact h
  rw [hUV]
  exact isCompact_iUnion fun i ↦ (hs i _ _ (Set.preimage_mono hUs)
    (hUo.preimage (hj i).continuous) ((hj i).isInducing.isCompact_preimage (hclosed i) hUc)
    (Set.preimage_mono hVs) (hVo.preimage (hj i).continuous)
    ((hj i).isInducing.isCompact_preimage (hclosed i) hVc)).image (hj i).continuous

namespace AlgebraicGeometry

/-- Every point of a coproduct of schemes lies in the image of one of the inclusions. -/
lemma exists_sigmaι_eq {σ : Type*} [Small.{u} σ] {Y : σ → Scheme.{u}} (z : (∐ Y :)) :
    ∃ i y, Sigma.ι Y i y = z :=
  (sigmaOpenCover Y).exists_eq z

/-- A finite coproduct of quasi-compact morphisms is quasi-compact. -/
lemma quasiCompact_sigmaDesc {ι : Type} [Finite ι] {Y : ι → Scheme.{u}} {X : Scheme.{u}}
    (p : ∀ i, Y i ⟶ X) (hp : ∀ i, QuasiCompact (p i)) : QuasiCompact (Sigma.desc p) where
  isCompact_preimage U hU hUc := by
    have hpre : (Sigma.desc p) ⁻¹' U = ⋃ i, Sigma.ι Y i '' (p i ⁻¹' U) := by
      ext z
      obtain ⟨i, y, rfl⟩ := exists_sigmaι_eq z
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
      constructor
      · intro h
        refine ⟨i, y, ?_, rfl⟩
        rwa [← Scheme.Hom.comp_apply, Sigma.ι_desc] at h
      · rintro ⟨k, y', h, hy'⟩
        rwa [← hy', ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    rw [hpre]
    exact isCompact_iUnion fun i ↦
      ((hp i).isCompact_preimage U hU hUc).image (Sigma.ι Y i).continuous

/-- A finite coproduct of quasi-separated morphisms is quasi-separated. -/
lemma quasiSeparated_sigmaDesc {ι : Type} [Finite ι] {Y : ι → Scheme.{u}} {X : Scheme.{u}}
    (p : ∀ i, Y i ⟶ X) (hp : ∀ i, QuasiSeparated (p i)) : QuasiSeparated (Sigma.desc p) := by
  rw [HasAffineProperty.eq_targetAffineLocally @QuasiSeparated]
  intro U
  have hpre (i : ι) : Sigma.ι Y i ⁻¹' (Sigma.desc p ⁻¹ᵁ U.1 : Set (∐ Y :)) = p i ⁻¹' U := by
    ext y
    rw [Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      Sigma.ι_desc, Set.mem_preimage]
  refine (isQuasiSeparated_iff_quasiSeparatedSpace _ (Sigma.desc p ⁻¹ᵁ U.1).isOpen).mp ?_
  refine IsQuasiSeparated.of_isOpenEmbedding_cover (fun i ↦ Sigma.ι Y i)
    (fun i ↦ (Sigma.ι Y i).isOpenEmbedding) (fun i k hik ↦ ?_) exists_sigmaι_eq fun i ↦ ?_
  · refine Set.disjoint_left.mpr fun _ ⟨y, hy⟩ ⟨y', hy'⟩ ↦ hik ?_
    exact congrArg Sigma.fst ((sigmaι_eq_iff Y i k y y').mp (hy.trans hy'.symm))
  · rw [hpre i]
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (p i ⁻¹ᵁ U.1).isOpen).mpr
      (HasAffineProperty.restrict (P := @QuasiSeparated) (hp i) U)

namespace Scheme.Etale

variable {X : Scheme.{u}}

/-- An object of `X.Etale` is qcqs if its structure morphism is quasi-compact and
quasi-separated. -/
def IsQcqs (Y : X.Etale) : Prop :=
  QuasiCompact Y.hom ∧ QuasiSeparated Y.hom

lemma IsQcqs.of_iso {Y Y' : X.Etale} (e : Y ≅ Y') (h : IsQcqs Y) : IsQcqs Y' :=
  ⟨(MorphismProperty.over_iso_iff _ ((Etale.forget X).mapIso e)).mp h.1,
    (MorphismProperty.over_iso_iff _ ((Etale.forget X).mapIso e)).mp h.2⟩

/-- The property of being étale, quasi-compact and quasi-separated. -/
abbrev etaleQcqs : MorphismProperty Scheme.{u} := @Etale ⊓ (@QuasiCompact ⊓ @QuasiSeparated)

instance : etaleQcqs.HasOfPostcompProperty etaleQcqs where
  of_postcomp f g hg hfg := by
    have := hg.2.2
    have := hfg.2.1
    have := hfg.2.2
    exact ⟨MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) f g hg.1 hfg.1,
      QuasiCompact.of_comp f g, QuasiSeparated.of_comp f g⟩

lemma isQcqs_of_isLimit {J : Type} [SmallCategory J] [FinCategory J] {F : J ⥤ X.Etale}
    (c : Cone F) (hc : IsLimit c) (hF : ∀ j, IsQcqs (F.obj j)) : IsQcqs c.pt := by
  let ι : etaleQcqs.Over ⊤ X ⥤ X.Etale := MorphismProperty.Over.changeProp X inf_le_left le_rfl
  have : PreservesFiniteLimits (ι ⋙ Etale.forget X) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget etaleQcqs ⊤ X))
  have : PreservesLimitsOfShape J ι :=
    preservesLimitsOfShape_of_reflects_of_preserves ι (Etale.forget X)
  let G : J ⥤ etaleQcqs.Over ⊤ X :=
    MorphismProperty.Comma.lift (F ⋙ MorphismProperty.Comma.forget _ _ _ _ _)
      (fun j ↦ ⟨(F.obj j).prop, hF j⟩) (fun _ ↦ trivial) (fun _ ↦ trivial)
  let e : G ⋙ ι ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)
  exact IsQcqs.of_iso (IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves ι (limit.isLimit G))
    hc e) (limit G).prop.2

instance : HasFiniteCoproducts X.Etale :=
  ⟨fun _ ↦ inferInstance⟩

lemma isQcqs_of_isColimit_cofan {ι : Type} [Finite ι] {Y : ι → X.Etale} (c : Cofan Y)
    (hc : IsColimit c) (h : ∀ i, IsQcqs (Y i)) : IsQcqs c.pt := by
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
  exact IsQcqs.of_iso (hW.coconePointUniqueUpToIso hc)
    ⟨quasiCompact_sigmaDesc p fun i ↦ (h i).1, quasiSeparated_sigmaDesc p fun i ↦ (h i).2⟩

lemma isQcqs_of_isColimit_binaryCofan {Y Y' : X.Etale} (c : BinaryCofan Y Y')
    (hc : IsColimit c) (h : IsQcqs Y) (h' : IsQcqs Y') : IsQcqs c.pt := by
  refine isQcqs_of_isColimit_cofan (Y := fun j : WalkingPair ↦ WalkingPair.casesOn (motive := fun _ ↦ X.Etale) j Y Y')
    c hc ?_
  rintro (_ | _)
  · exact h
  · exact h'

lemma isEmpty_of_isInitial {Y : X.Etale} (h : IsInitial Y) : IsEmpty Y.left := by
  have : IsEmpty (Etale.mk (Scheme.emptyTo X)).left :=
    inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  exact ⟨fun y ↦ isEmptyElim ((h.to (Etale.mk (Scheme.emptyTo X))).left y)⟩

lemma isQcqs_of_isInitial {Y : X.Etale} (h : IsInitial Y) : IsQcqs Y := by
  have := isEmpty_of_isInitial h
  have : IsOpenImmersion Y.hom := isOpenImmersion_of_isEmpty Y.hom
  exact ⟨⟨fun _ _ _ ↦ Set.subsingleton_of_subsingleton.isCompact⟩, inferInstance⟩

lemma isQcqs_of_isAffine [QuasiSeparatedSpace X] (Y : X.Etale) [IsAffine Y.left] :
    IsQcqs Y := by
  have : QuasiSeparatedSpace ((Functor.fromPUnit X).obj Y.right) :=
    inferInstanceAs (QuasiSeparatedSpace X)
  exact ⟨quasiCompact_of_compactSpace Y.hom, QuasiSeparated.of_quasiSeparatedSpace Y.hom⟩

lemma compactSpace_of_isQcqs [CompactSpace X] {Y : X.Etale} (h : IsQcqs Y) :
    CompactSpace Y.left := by
  have := h.1
  have : CompactSpace ((Functor.fromPUnit X).obj Y.right) := inferInstanceAs (CompactSpace X)
  exact QuasiCompact.compactSpace_of_compactSpace Y.hom

/-- A sieve on an étale `X`-scheme is a covering sieve iff its members jointly cover all
points. -/
lemma mem_smallEtaleTopology_iff {T : X.Etale} (S : Sieve T) :
    S ∈ X.smallEtaleTopology T ↔
      ∀ x : T.left, ∃ (Z : X.Etale) (g : Z ⟶ T), S g ∧ x ∈ Set.range g.left := by
  constructor
  · intro hS x
    let A := Σ Z : X.Etale, {g : Z ⟶ T // S g}
    have hcov := (ofArrows_mem_smallEtaleTopology_iff (fun a : A ↦ a.2.1)).mp
      (GrothendieckTopology.superset_covering _
        (fun Z g hg ↦ Sieve.ofArrows_mk _ _ (⟨Z, g, hg⟩ : A)) hS)
    have hx : x ∈ ⋃ a : A, Set.range a.2.1.left := by
      rw [hcov]
      exact Set.mem_univ x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    exact ⟨a.1, a.2.1, a.2.2, ha⟩
  · intro h
    choose Z g hg hx using h
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff g).mpr ?_)
    · rintro _ _ ⟨W, a, b, ⟨x⟩, rfl⟩
      exact S.downward_closed (hg x) a
    · exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩

lemma mem_smallEtaleTopology_of_surjective {T T' : X.Etale} (π : T' ⟶ T)
    (h : Surjective π.left) {S : Sieve T} (hS : S π) : S ∈ X.smallEtaleTopology T :=
  (mem_smallEtaleTopology_iff S).mpr fun x ↦ ⟨T', π, hS, h.surj x⟩

/-- A covering sieve of a quasi-compact étale `X`-scheme contains a finite jointly surjective
family of étale `X`-schemes with affine source. -/
lemma exists_finite_affine_of_mem_smallEtaleTopology {M : X.Etale} [CompactSpace M.left]
    (S : Sieve M) (hS : S ∈ X.smallEtaleTopology M) :
    ∃ (k : ℕ) (V : Fin k → X.Etale) (φ : ∀ i, V i ⟶ M),
      (∀ i, S (φ i)) ∧ (∀ i, IsAffine (V i).left) ∧
        ∀ x : M.left, ∃ (i : Fin k) (y : (V i).left), (φ i).left y = x := by
  classical
  have h' (x : M.left) : ∃ (Z : X.Etale) (g : Z ⟶ M) (z : Z.left), S g ∧ g.left z = x := by
    obtain ⟨Z, g, hg, z, hz⟩ := (mem_smallEtaleTopology_iff S).mp hS x
    exact ⟨Z, g, z, hg, hz⟩
  choose Z g z hg hz using h'
  choose i w hw using fun x ↦ (Z x).left.affineCover.exists_eq (z x)
  let V' (x : M.left) : X.Etale := MorphismProperty.Over.mk ⊤
    ((Z x).left.affineCover.f (i x) ≫ (Z x).hom)
    (MorphismProperty.comp_mem _ _ _ inferInstance (Z x).prop)
  let ψ (x : M.left) : V' x ⟶ Z x :=
    MorphismProperty.Over.homMk ((Z x).left.affineCover.f (i x)) rfl
  have hmem (x : M.left) : x ∈ Set.range (ψ x ≫ g x).left :=
    ⟨w x, (congrArg (g x).left (hw x)).trans (hz x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (ψ x ≫ g x).left)
    (fun x ↦ (ψ x ≫ g x).left.isOpenMap.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  let e := t.equivFin
  refine ⟨t.card, fun k ↦ V' (e.symm k), fun k ↦ ψ _ ≫ g _, fun k ↦ S.downward_closed (hg _) _,
    fun k ↦ inferInstanceAs (IsAffine ((Z _).left.affineCover.X _)), fun x ↦ ?_⟩
  obtain ⟨a, ha, y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨e ⟨a, ha⟩, ?_⟩
  dsimp only
  rw [Equiv.symm_apply_apply]
  exact ⟨y, hy⟩

end Scheme.Etale

end AlgebraicGeometry
