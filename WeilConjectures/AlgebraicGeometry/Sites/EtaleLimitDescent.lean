/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale data at a cofiltered limit of schemes

Let `X = lim Dⱼ` be a cofiltered limit of schemes with affine transition maps. This file
collects the finite-presentation data which descends from `X` to some stage `Dⱼ`, in the form in
which it is used for the continuity of étale sections
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`).

## Main results

- `AlgebraicGeometry.exists_etale_isPullback_of_isAffine`: if all `Dⱼ` are affine, every étale
  `X`-scheme is, around any of its points, dominated by the base change of an affine scheme
  étale over some `Dⱼ`. The proof writes the étale `X`-scheme locally as `Spec` of a standard
  étale algebra over `Γ(X) = colim Γ(Dⱼ)`, whose finitely many coefficients come from a stage.
- `AlgebraicGeometry.exists_etale_refinement_of_isLimit`: the same for a scheme étale over the
  base change `V ×_{Dₖ} X` of a scheme `V` étale over a stage `Dₖ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Étale schemes over an affine limit are locally dominated by base changes from a stage.**
Let `X = lim Aᵢ` be a cofiltered limit of affine schemes and `β : Z ⟶ X` étale. Every point of
`Z` lies in the image of a morphism `γ : E ×_{Aᵢ} X ⟶ Z` over `X` from the base change of an
affine scheme `E` étale over some `Aᵢ`. -/
theorem exists_etale_isPullback_of_isAffine {I : Type u} [Category.{u} I] [IsCofiltered I]
    (A : I ⥤ Scheme.{u}) [∀ i, IsAffine (A.obj i)] (c : Cone A) (hc : IsLimit c)
    {Z : Scheme.{u}} (β : Z ⟶ c.pt) [Etale β] (z : Z) :
    ∃ (i : I) (E : Scheme.{u}) (_ : IsAffine E) (q : E ⟶ A.obj i) (_ : Etale q)
      (E' : Scheme.{u}) (π₁ : E' ⟶ E) (π₂ : E' ⟶ c.pt) (_ : IsPullback π₁ π₂ q (c.π.app i))
      (γ : E' ⟶ Z) (_ : IsOpenImmersion γ), γ ≫ β = π₂ ∧ z ∈ Set.range γ := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- a standard étale chart of `Z` over `Spec Γ(X)` around `z`
  obtain ⟨P, e, heo, he, hz⟩ :=
    Etale.exists_standardEtalePair_isOpenImmersion (β ≫ c.pt.isoSpec.hom) z
  -- `Γ(X)` is the colimit of the `Γ(Aᵢ)`
  obtain ⟨hcol⟩ := nonempty_isColimit_Γ_mapCocone A c hc
  have hrep (b : Γ(c.pt, ⊤)) : ∃ (i : I) (s : Γ(A.obj i, ⊤)), (c.π.app i).appTop s = b := by
    obtain ⟨⟨i⟩, s, hs⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) hcol) b
    exact ⟨i, s, hs⟩
  choose i s hs using hrep
  -- the finitely many coefficients of `P` come from a common stage `i₀`
  let S : Finset Γ(c.pt, ⊤) := P.f.coeffs ∪ P.g.coeffs
  obtain ⟨i₀, hi₀⟩ := IsCofiltered.inf_objs_exists (S.image i)
  have hmem (b : Γ(c.pt, ⊤)) (hb : b ∈ S) : b ∈ Set.range (c.π.app i₀).appTop := by
    obtain ⟨g⟩ := hi₀ (Finset.mem_image_of_mem i hb)
    refine ⟨(A.map g).appTop (s b), ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w g]
    exact hs b
  let R := Γ(A.obj i₀, ⊤)
  let _ : Algebra R Γ(c.pt, ⊤) := (c.π.app i₀).appTop.hom.toAlgebra
  have hf : (P.f.coeffs : Set Γ(c.pt, ⊤)) ⊆ Set.range (algebraMap R Γ(c.pt, ⊤)) :=
    fun b hb ↦ hmem b (Finset.mem_union_left _ hb)
  have hg : (P.g.coeffs : Set Γ(c.pt, ⊤)) ⊆ Set.range (algebraMap R Γ(c.pt, ⊤)) :=
    fun b hb ↦ hmem b (Finset.mem_union_right _ hb)
  obtain ⟨Q, ⟨ε⟩⟩ := StandardEtalePair.exists_algEquiv_tensor_ring_of_coeffs_subset P hf hg
  -- the pushout square of rings `R → Γ(X), Q.Ring → P.Ring`
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Γ(c.pt, ⊤)))
      (CommRingCat.ofHom (algebraMap R Q.Ring))
      (CommRingCat.ofHom (algebraMap Γ(c.pt, ⊤) P.Ring))
      (CommRingCat.ofHom (ε.toRingHom.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := Γ(c.pt, ⊤)) (B := Q.Ring)).toRingHom)) := by
    refine (CommRingCat.isPushout_tensorProduct R Γ(c.pt, ⊤) Q.Ring).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ε.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change ε (x ⊗ₜ 1) = algebraMap _ _ x
      rw [← ε.commutes]
      rfl
    · ext x
      simp
  have hqet : Etale (Spec.map (CommRingCat.ofHom (algebraMap R Q.Ring))) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale R Q.Ring)))
  have hsq : IsPullback
      (Spec.map (CommRingCat.ofHom (ε.toRingHom.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := Γ(c.pt, ⊤)) (B := Q.Ring)).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(c.pt, ⊤) P.Ring)) ≫ c.pt.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap R Q.Ring)) ≫ (A.obj i₀).isoSpec.inv)
      (c.π.app i₀) := by
    refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip.of_iso (Iso.refl _) (Iso.refl _)
      c.pt.isoSpec.symm (A.obj i₀).isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [← Scheme.isoSpec_inv_naturality]
      rfl
  refine ⟨i₀, _, inferInstance, _, inferInstance, _, _, _, hsq, e, heo, ?_, hz⟩
  rw [← he]
  simp

section Stage

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **Étale schemes over a base change to the limit are locally dominated by base changes from a
stage.** Let `X = lim Dⱼ` be a cofiltered limit with affine transition maps, `p : V ⟶ Dₖ` étale
and `β : Z ⟶ V ×_{Dₖ} X` étale. Every point of `Z` lies in the image of a morphism
`γ : E ×_{Dₖ'} X ⟶ Z` over `V ×_{Dₖ} X` from the base change of an affine scheme `E` étale over
a later stage `Dₖ'` and mapping to `V`. -/
theorem exists_etale_refinement_of_isLimit {k : J} {V : Scheme.{u}} (p : V ⟶ D.obj k)
    [Etale p] {Z : Scheme.{u}} (β : Z ⟶ pullback p (c.π.app k)) [Etale β] (z : Z) :
    ∃ (k' : J) (f : k' ⟶ k) (E : Scheme.{u}) (_ : IsAffine E) (q : E ⟶ D.obj k') (_ : Etale q)
      (e : E ⟶ V) (he : e ≫ p = q ≫ D.map f) (E' : Scheme.{u}) (π₁ : E' ⟶ E)
      (π₂ : E' ⟶ c.pt) (hπ : IsPullback π₁ π₂ q (c.π.app k')) (γ : E' ⟶ Z)
      (_ : IsOpenImmersion γ),
      γ ≫ β = pullback.lift (π₁ ≫ e) π₂
        (by rw [Category.assoc, he, reassoc_of% hπ.w, c.w f]) ∧ z ∈ Set.range γ := by
  -- an affine open `O` of `V` around the image of `z`
  obtain ⟨O, hO, hxO, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := V) (x := pullback.fst p (c.π.app k) (β z)) (U := ⊤) trivial
  have : IsAffine O := hO
  let pO : O.toScheme ⟶ D.obj k := O.ι ≫ p
  -- the open `Z_O` of `Z` lying over `O`
  let ZO : Z.Opens := (β ≫ pullback.fst p (c.π.app k)) ⁻¹ᵁ O
  have hzO : z ∈ ZO := hxO
  let r : ZO.toScheme ⟶ O.toScheme := (β ≫ pullback.fst p (c.π.app k)).resLE O ZO le_rfl
  have hr : r ≫ O.ι = ZO.ι ≫ β ≫ pullback.fst p (c.π.app k) := Scheme.Hom.resLE_comp_ι _ _
  let β' : ZO.toScheme ⟶ pullback pO (c.π.app k) :=
    pullback.lift r (ZO.ι ≫ β ≫ pullback.snd _ _) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition, ← reassoc_of% hr])
  have hβ'₂ : β' ≫ pullback.snd pO (c.π.app k) = ZO.ι ≫ β ≫ pullback.snd _ _ :=
    pullback.lift_snd _ _ _
  have : Etale (β' ≫ pullback.snd pO (c.π.app k)) := by
    rw [hβ'₂]
    infer_instance
  have : Etale β' := Etale.of_comp β' (pullback.snd pO (c.π.app k))
  have (j : Over k) : IsAffine ((baseChangeDiagram D pO).obj j) :=
    inferInstanceAs (IsAffine (pullback pO (D.map j.hom)))
  obtain ⟨i, E, hE, q, hq, E', π₁, π₂, hπ, γ', hγ'o, hγ', hz'⟩ :=
    exists_etale_isPullback_of_isAffine (baseChangeDiagram D pO) (baseChangeCone D c pO)
      (isLimitBaseChangeCone D c pO hc) β' ⟨z, hzO⟩
  have := hγ'o
  have hπ' : IsPullback π₁ (π₂ ≫ pullback.snd pO (c.π.app k))
      (q ≫ pullback.snd pO (D.map i.hom)) (c.π.app i.left) :=
    hπ.paste_vert (isPullback_baseChangeCone_π D c pO i)
  have he : (q ≫ pullback.fst pO (D.map i.hom) ≫ O.ι) ≫ p =
      (q ≫ pullback.snd pO (D.map i.hom)) ≫ D.map i.hom := by
    simp only [Category.assoc]
    rw [← pullback.condition]
  refine ⟨i.left, i.hom, E, hE, q ≫ pullback.snd pO (D.map i.hom), inferInstance,
    q ≫ pullback.fst pO (D.map i.hom) ≫ O.ι, he, E', π₁, π₂ ≫ pullback.snd pO (c.π.app k), hπ',
    γ' ≫ ZO.ι, inferInstance, ?_, ?_⟩
  · have h1 : r = β' ≫ pullback.fst pO (c.π.app k) := (pullback.lift_fst _ _ _).symm
    have key : ZO.ι ≫ β ≫ pullback.fst p (c.π.app k) =
        β' ≫ pullback.fst pO (c.π.app k) ≫ O.ι := by
      rw [← hr, h1, Category.assoc]
    have h2 : π₂ ≫ pullback.fst pO (c.π.app k) ≫ O.ι =
        π₁ ≫ q ≫ pullback.fst pO (D.map i.hom) ≫ O.ι := by
      have h3 : (baseChangeCone D c pO).π.app i ≫ pullback.fst pO (D.map i.hom) =
          pullback.fst pO (c.π.app k) := baseChangeCone_π_app_fst D c pO i
      calc π₂ ≫ pullback.fst pO (c.π.app k) ≫ O.ι
          = π₂ ≫ ((baseChangeCone D c pO).π.app i ≫ pullback.fst pO (D.map i.hom)) ≫ O.ι := by
            rw [h3]
        _ = (π₁ ≫ q) ≫ pullback.fst pO (D.map i.hom) ≫ O.ι := by
            rw [hπ.w]; simp only [Category.assoc]
        _ = _ := by simp only [Category.assoc]
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp only [Category.assoc]
      rw [key]
      exact ((reassoc_of% hγ') _).trans h2
    · rw [pullback.lift_snd]
      simp only [Category.assoc]
      rw [← hβ'₂]
      exact (reassoc_of% hγ') (pullback.snd pO (c.π.app k))
  · obtain ⟨w, hw⟩ := hz'
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]; rfl⟩

section OverBase

variable [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
  {R : Scheme.{u}} (π : D ⟶ (Functor.const J).obj R)

/-- (Implementation) The structure morphism to `R` of the base change of the diagram along a
morphism `q : E ⟶ Dₖ`. -/
@[simps]
noncomputable def baseChangeDiagramToBase {k : J} {E : Scheme.{u}} (q : E ⟶ D.obj k) :
    baseChangeDiagram D q ⟶ (Functor.const (Over k)).obj R where
  app j := pullback.snd q (D.map j.hom) ≫ π.app j.left
  naturality {j j'} g := by
    have h := π.naturality g.left
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h ⊢
    rw [baseChangeDiagram_map_snd_assoc, h]

omit [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] in
include hc in
/-- **Morphisms to a scheme of finite presentation over the base descend to a stage.** Let
`q : E ⟶ Dₖ` with `E` quasi-compact and quasi-separated, and let `u : U ⟶ R` be locally of
finite presentation. Every `R`-morphism `E ×_{Dₖ} X ⟶ U` factors through `E ×_{Dₖ} Dₖ'` for some
`k' ⟶ k`. -/
theorem exists_hom_descent_of_isLimit {k : J} {E : Scheme.{u}} (q : E ⟶ D.obj k)
    [CompactSpace E] [QuasiSeparatedSpace E] {U : Scheme.{u}} (u : U ⟶ R)
    [LocallyOfFinitePresentation u] (φ : pullback q (c.π.app k) ⟶ U)
    (hφ : φ ≫ u = pullback.snd q (c.π.app k) ≫ c.π.app k ≫ π.app k) :
    ∃ (k' : J) (f : k' ⟶ k) (ψ : pullback q (D.map f) ⟶ U),
      ψ ≫ u = pullback.snd q (D.map f) ≫ π.app k' ∧
        pullback.map q (c.π.app k) q (D.map f) (𝟙 _) (c.π.app k') (𝟙 _) (by simp)
          (by simp) ≫ ψ = φ := by
  obtain ⟨j, g, hg, hgu⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D q) (baseChangeDiagramToBase D π q) u (baseChangeCone D c q)
    (isLimitBaseChangeCone D c q hc) φ (by
      ext j
      have h₁ := π.naturality j.hom
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h₁
      simp only [Functor.const_obj_obj, NatTrans.comp_app, baseChangeCone_π_app,
        baseChangeDiagramToBase_app, Functor.const_map_app, hφ]
      rw [pullback.lift_snd_assoc, ← h₁, Category.assoc, c.w_assoc])
  exact ⟨j.left, j.hom, g, hgu, hg⟩

omit [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] in
include hc in
/-- **Equalities of morphisms to a scheme of finite type over the base descend to a stage.** -/
theorem exists_eq_descent_of_isLimit {k : J} {E : Scheme.{u}} (q : E ⟶ D.obj k)
    [CompactSpace E] {U : Scheme.{u}} (u : U ⟶ R) [LocallyOfFiniteType u] (ψ₁ ψ₂ : E ⟶ U)
    (h₁ : ψ₁ ≫ u = q ≫ π.app k) (h₂ : ψ₂ ≫ u = q ≫ π.app k)
    (h : pullback.fst q (c.π.app k) ≫ ψ₁ = pullback.fst q (c.π.app k) ≫ ψ₂) :
    ∃ (k' : J) (f : k' ⟶ k), pullback.fst q (D.map f) ≫ ψ₁ = pullback.fst q (D.map f) ≫ ψ₂ := by
  obtain ⟨j, hj, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D q) (baseChangeDiagramToBase D π q) u (baseChangeCone D c q)
    (isLimitBaseChangeCone D c q hc) (i := Over.mk (𝟙 k))
    (pullback.fst _ _ ≫ ψ₁) (pullback.fst _ _ ≫ ψ₂)
    (by simp [h₁, pullback.condition_assoc]) (by simp [h₂, pullback.condition_assoc])
    (by rw [baseChangeCone_π_app_fst_assoc, baseChangeCone_π_app_fst_assoc, h])
  exact ⟨j.left, j.hom, by simpa using heq⟩

end OverBase

section Cover

variable [∀ j, CompactSpace (D.obj j)]

omit [∀ j, CompactSpace (D.obj j)] in
include hc in
/-- **Coverings descend to a stage.** Let `p : V ⟶ Dₖ` with `V` quasi-compact and let
`eᵢ : Eᵢ ⟶ V` be finitely many étale morphisms. If every point of `V ×_{Dₖ} X` maps into one of
the images of the `eᵢ`, then from some stage `k'` on, every point of `V ×_{Dₖ} Dₖ''` does. -/
theorem exists_forall_mem_range_of_isLimit {k : J} {V : Scheme.{u}} (p : V ⟶ D.obj k)
    [CompactSpace V] {ι : Type*} {E : ι → Scheme.{u}} (e : ∀ i, E i ⟶ V) [∀ i, Etale (e i)]
    (h : ∀ x : ↥(pullback p (c.π.app k)), ∃ i, pullback.fst p (c.π.app k) x ∈ Set.range (e i)) :
    ∃ (k' : J) (f : k' ⟶ k), ∀ (k'' : J) (g : k'' ⟶ k') (x : ↥(pullback p (D.map (g ≫ f)))),
      ∃ i, pullback.fst p (D.map (g ≫ f)) x ∈ Set.range (e i) := by
  let Ω : V.Opens := ⨆ i, ⟨Set.range (e i), (e i).isOpenMap.isOpen_range⟩
  have hΩ (y : V) : y ∈ Ω ↔ ∃ i, y ∈ Set.range (e i) := by
    simp [Ω]
  obtain ⟨j, fj, hj⟩ := exists_map_eq_top (baseChangeDiagram D p) (baseChangeCone D c p)
    (isLimitBaseChangeCone D c p hc) (i := Over.mk (𝟙 k))
    (pullback.fst p (D.map (𝟙 k)) ⁻¹ᵁ Ω) (by
      ext x
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      change (((baseChangeCone D c p).π.app (Over.mk (𝟙 k)) ≫
        pullback.fst p (D.map (𝟙 k))) x) ∈ Ω
      have e₁ : (baseChangeCone D c p).π.app (Over.mk (𝟙 k)) ≫ pullback.fst p (D.map (𝟙 k)) =
          pullback.fst p (c.π.app k) := baseChangeCone_π_app_fst D c p (Over.mk (𝟙 k))
      rw [e₁, hΩ]
      exact h x)
  refine ⟨j.left, j.hom, fun k'' g x ↦ ?_⟩
  let y : ↥(pullback p (D.map j.hom)) := pullback.map p (D.map (g ≫ j.hom)) p (D.map j.hom)
    (𝟙 _) (D.map g) (𝟙 _) (by simp) (by simp) x
  have hy : y ∈ (baseChangeDiagram D p).map fj ⁻¹ᵁ pullback.fst p (D.map (𝟙 k)) ⁻¹ᵁ Ω := by
    rw [hj]
    trivial
  rw [← hΩ]
  change ((baseChangeDiagram D p).map fj ≫ pullback.fst p (D.map (𝟙 k))) y ∈ Ω at hy
  have e₂ : (baseChangeDiagram D p).map fj ≫ pullback.fst p (D.map (𝟙 k)) =
      pullback.fst p (D.map j.hom) := baseChangeDiagram_map_fst D p fj
  have hxy : pullback.fst p (D.map j.hom) y = pullback.fst p (D.map (g ≫ j.hom)) x := by
    change (pullback.map p (D.map (g ≫ j.hom)) p (D.map j.hom) (𝟙 _) (D.map g) (𝟙 _)
      (by simp) (by simp) ≫ pullback.fst p (D.map j.hom)) x = _
    rw [pullback.lift_fst, Category.comp_id]
  rw [e₂] at hy
  rw [← hxy]
  exact hy

end Cover

section Global

/-- If `W` is an open of `Y` on which `p : Y ⟶ S` is étale, then the base change `p'` of `p` is
étale on the preimage of `W`. -/
lemma etale_ι_preimage_comp_of_isPullback {Y Y' S S' : Scheme.{u}} {ρ : Y' ⟶ Y} {p' : Y' ⟶ S'}
    {p : Y ⟶ S} {σ : S' ⟶ S} (H : IsPullback ρ p' p σ) (W : Y.Opens) [Etale (W.ι ≫ p)] :
    Etale ((ρ ⁻¹ᵁ W).ι ≫ p') :=
  MorphismProperty.of_isPullback ((isPullback_morphismRestrict ρ W).paste_vert H) ‹_›

/-- Étaleness of the second projection of a pullback square only depends on the cospan. -/
lemma etale_of_isPullback_of_isPullback {P P' X Y Z : Scheme.{u}} {a : P ⟶ X} {l : P ⟶ Y}
    {a' : P' ⟶ X} {l' : P' ⟶ Y} {r : X ⟶ Z} {σ : Y ⟶ Z} (h : IsPullback a l r σ)
    (h' : IsPullback a' l' r σ) [Etale l] : Etale l' := by
  rw [← h'.isoIsPullback_hom_snd _ _ h]
  infer_instance

variable [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc in
/-- (Implementation) **Étaleness of a finite-stage model spreads out locally.** Let
`h : V ⟶ Y` exhibit `V ⟶ X` as the base change of `p : Y ⟶ D_{i₀}` (of finite presentation,
quasi-compact and quasi-separated), with `V ⟶ X` étale. Around every point of `V` there is a
stage `Y ×_{D_{i₀}} Dⱼ` of the base changed system and an open of it on which the projection to
`Dⱼ` is étale and through which the point maps. -/
lemma exists_etale_opens_of_isPullback {i₀ : J} {V Y : Scheme.{u}} {g : V ⟶ c.pt}
    {p : Y ⟶ D.obj i₀} {h : V ⟶ Y} [Etale g] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p] (H : IsPullback h g p (c.π.app i₀)) (x : V) :
    ∃ (j : Over i₀) (W : (pullback p (D.map j.hom)).Opens),
      Etale (W.ι ≫ pullback.snd p (D.map j.hom)) ∧ x ∈ isPullbackLift D c j.hom H ⁻¹ᵁ W := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  -- `V` is the limit of the stages `Y ×_{D_{i₀}} Dⱼ`
  let L := (baseChangeCone D c p).extend H.isoPullback.hom
  have hL : IsLimit L := (isLimitBaseChangeCone D c p hc).ofIsoLimit
    (Cone.ext H.isoPullback.symm (fun j ↦ by simp [L, Cone.extend]))
  have hLj (j : Over i₀) : L.π.app j = isPullbackLift D c j.hom H := by
    apply pullback.hom_ext <;> simp [L, Cone.extend, IsPullback.isoPullback_hom_fst]
  -- an open chart of `V` around `x` which is the base change of an affine étale scheme
  let β : V ⟶ pullback (𝟙 (D.obj i₀)) (c.π.app i₀) :=
    pullback.lift (g ≫ c.π.app i₀) g (by simp)
  have : Etale β := by
    have : Etale (β ≫ pullback.snd (𝟙 (D.obj i₀)) (c.π.app i₀)) := by
      rw [pullback.lift_snd]
      infer_instance
    exact Etale.of_comp β (pullback.snd _ _)
  obtain ⟨k', f₀, E, hE, q, hq, e, he, E', π₁, π₂, hπ, γ, hγo, hγ, hx⟩ :=
    exists_etale_refinement_of_isLimit D c hc (𝟙 (D.obj i₀)) β x
  have hγg : γ ≫ g = π₂ := by
    have := hγ =≫ pullback.snd _ _
    simpa [β] using this
  have : IsAffineHom (c.π.app k') := isAffineHom_π_app D c hc k'
  have : IsAffineHom π₁ := MorphismProperty.of_isPullback hπ.flip inferInstance
  have : IsAffine E' := isAffine_of_isAffineHom π₁
  have hO : IsCompact (γ.opensRange : Set V) := by
    simpa using isCompact_range γ.continuous
  -- the chart descends to an open `Ω` of a stage
  obtain ⟨j, Ω, hΩc, hΩ⟩ := exists_preimage_eq (baseChangeDiagram D p) L hL γ.opensRange hO
  rw [hLj] at hΩ
  have : CompactSpace Ω.toScheme := isCompact_iff_compactSpace.mp hΩc
  have : QuasiSeparatedSpace Ω.toScheme := quasiSeparatedSpace_of_quasiSeparated Ω.ι
  -- two models of the chart: `E` at the stage `k'` and `Ω` at the stage `j`
  let T := (isPullbackLift D c j.hom H ⁻¹ᵁ Ω).toScheme
  let e₁ : T ≅ E' := V.isoOfEq hΩ ≪≫ γ.isoOpensRange.symm
  have he₁ : e₁.hom ≫ γ = (isPullbackLift D c j.hom H ⁻¹ᵁ Ω).ι := by
    simp [e₁]
  have M₂ : IsPullback (e₁.inv ≫ (isPullbackLift D c j.hom H ∣_ Ω)) π₂
      (Ω.ι ≫ pullback.snd p (D.map j.hom)) (c.π.app j.left) := by
    refine ((isPullback_morphismRestrict _ Ω).paste_vert
      (isPullback_isPullbackLift j.hom H)).of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← hγg, reassoc_of% he₁]
    simp
  -- the two models become isomorphic at a later stage
  let K := IsCofiltered.min k' j.left
  have M₁' := isPullback_isPullbackLift (IsCofiltered.minToLeft k' j.left) hπ
  have M₂' := isPullback_isPullbackLift (IsCofiltered.minToRight k' j.left) M₂
  obtain ⟨k'', f'', hiso⟩ := exists_iso_of_isPullback hc M₁' M₂'
  obtain ⟨eiso, heiso, -⟩ := hiso (IsPullback.of_hasPullback _ (D.map f''))
    (isPullbackLift_fst f'' M₁') (isPullbackLift_snd f'' M₁')
    (IsPullback.of_hasPullback _ (D.map f'')) (isPullbackLift_fst f'' M₂')
    (isPullbackLift_snd f'' M₂')
  have : Etale (pullback.snd (pullback.snd (Ω.ι ≫ pullback.snd p (D.map j.hom))
      (D.map (IsCofiltered.minToRight k' j.left))) (D.map f'')) := by
    rw [(Iso.eq_inv_comp eiso).mpr heiso]
    infer_instance
  -- the corresponding open of the stage `m = k''` is étale over `D_{k''}`
  let φ : Over.mk (f'' ≫ IsCofiltered.minToRight k' j.left ≫ j.hom) ⟶ j :=
    Over.homMk (f'' ≫ IsCofiltered.minToRight k' j.left)
  have hW := (isPullback_morphismRestrict ((baseChangeDiagram D p).map φ) Ω).paste_vert
    (isPullback_baseChangeDiagram_map D p φ)
  have hφ : D.map φ.left = D.map f'' ≫ D.map (IsCofiltered.minToRight k' j.left) := by
    simp [φ]
  rw [hφ] at hW
  refine ⟨_, (baseChangeDiagram D p).map φ ⁻¹ᵁ Ω,
    etale_of_isPullback_of_isPullback ((IsPullback.of_hasPullback _ _).paste_horiz
      (IsPullback.of_hasPullback _ _)) hW, ?_⟩
  have hLφ := L.w φ
  rw [hLj, hLj] at hLφ
  change x ∈ (isPullbackLift D c _ H ≫ (baseChangeDiagram D p).map φ) ⁻¹ᵁ Ω
  rw [hLφ, hΩ]
  exact hx

include hc in
/-- **Quasi-compact quasi-separated étale schemes descend to a stage.** Let `X = lim Dⱼ` be a
cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps and let
`g : V ⟶ X` be étale, quasi-compact and quasi-separated. Then `V` is the base change
`V ≅ Y ×_{Dⱼ} X` of a quasi-compact quasi-separated scheme `Y` étale over some stage `Dⱼ`.

The scheme `V` is the base change of a scheme `Y` of finite presentation over a stage
(`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`). Around each point, `V` has
an open chart which is the base change of an affine scheme étale over a stage
(`AlgebraicGeometry.exists_etale_refinement_of_isLimit`); the chart descends to an open of a
stage of `Y`, which is isomorphic to the étale model at a later stage
(`AlgebraicGeometry.exists_iso_of_isPullback`). Finitely many such opens cover a late stage of
`Y` (`AlgebraicGeometry.exists_map_eq_top`), which is therefore étale. -/
theorem exists_etale_isPullback_of_isLimit {V : Scheme.{u}} (g : V ⟶ c.pt) [Etale g]
    [QuasiCompact g] [QuasiSeparated g] :
    ∃ (j : J) (Y : Scheme.{u}) (p : Y ⟶ D.obj j) (_ : Etale p) (_ : CompactSpace Y)
      (_ : QuasiSeparatedSpace Y) (h : V ⟶ Y), IsPullback h g p (c.π.app j) := by
  classical
  obtain ⟨i₀, Y, p, hp, hpc, hps, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace g
  let L := (baseChangeCone D c p).extend H.isoPullback.hom
  have hL : IsLimit L := (isLimitBaseChangeCone D c p hc).ofIsoLimit
    (Cone.ext H.isoPullback.symm (fun j ↦ by simp [L, Cone.extend]))
  have hLj (j : Over i₀) : L.π.app j = isPullbackLift D c j.hom H := by
    apply pullback.hom_ext <;> simp [L, Cone.extend, IsPullback.isoPullback_hom_fst]
  choose j W hW hx using exists_etale_opens_of_isPullback D c hc H
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (isPullbackLift D c (j x).hom H ⁻¹ᵁ W x : Set V))
    (fun x ↦ (isPullbackLift D c (j x).hom H ⁻¹ᵁ W x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  obtain ⟨j₀, hj₀⟩ := IsCofiltered.inf_objs_exists (T.image j)
  have φ (x : T) : j₀ ⟶ j x := (hj₀ (Finset.mem_image_of_mem _ x.2)).some
  -- the étale opens, transported to the common stage `j₀`
  let W' (x : T) : ((baseChangeDiagram D p).obj j₀).Opens :=
    (baseChangeDiagram D p).map (φ x) ⁻¹ᵁ W x
  have hW' (x : T) : Etale ((W' x).ι ≫ pullback.snd p (D.map j₀.hom)) :=
    etale_ι_preimage_comp_of_isPullback (isPullback_baseChangeDiagram_map D p (φ x)) _
  have hU : L.π.app j₀ ⁻¹ᵁ (⨆ x : T, W' x) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hxT, hy⟩ : ∃ x ∈ T, y ∈ isPullbackLift D c (j x).hom H ⁻¹ᵁ W x := by
      simpa using hT (Set.mem_univ y)
    rw [Scheme.Hom.preimage_iSup]
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxT⟩, ?_⟩
    change y ∈ (L.π.app j₀ ≫ (baseChangeDiagram D p).map (φ ⟨x, hxT⟩)) ⁻¹ᵁ W x
    rw [L.w, hLj]
    exact hy
  obtain ⟨j₁, f₁, hj₁⟩ := exists_map_eq_top (baseChangeDiagram D p) L hL _ hU
  have : Etale (pullback.snd p (D.map j₁.hom)) := by
    refine IsZariskiLocalAtSource.of_iSup_eq_top
      (fun x : T ↦ (baseChangeDiagram D p).map f₁ ⁻¹ᵁ W' x) ?_ fun x ↦ ?_
    · rw [← Scheme.Hom.preimage_iSup]
      exact hj₁
    · have := hW' x
      exact etale_ι_preimage_comp_of_isPullback (isPullback_baseChangeDiagram_map D p f₁) _
  exact ⟨j₁.left, pullback p (D.map j₁.hom), pullback.snd _ _, inferInstance, inferInstance,
    inferInstance, isPullbackLift D c j₁.hom H, isPullback_isPullbackLift j₁.hom H⟩

end Global

include hc in
/-- **Finite-presentation data at an inverse limit.** Let `X = lim Dⱼ` be a cofiltered limit of
quasi-compact quasi-separated schemes over `R` with affine transition maps. Then:
1. *(étale objects)* every scheme `Z` étale over the base change `V ×_{Dₖ} X` of a scheme `V`
   étale over a stage is, around each of its points, dominated over `V ×_{Dₖ} X` by the base
   change `E ×_{Dₖ'} X` of an affine scheme `E` étale over a later stage `Dₖ'` and mapping to
   `V` (`AlgebraicGeometry.exists_etale_refinement_of_isLimit`);
2. *(morphisms)* for `E` quasi-compact and quasi-separated over a stage `Dₖ` and `U` locally of
   finite presentation over `R`, every `R`-morphism `E ×_{Dₖ} X ⟶ U` descends to
   `E ×_{Dₖ} Dₖ'` for some `k' ⟶ k` (`AlgebraicGeometry.exists_hom_descent_of_isLimit`);
3. *(equalities)* two `R`-morphisms `E ⟶ U` from a quasi-compact scheme over a stage `Dₖ` to a
   scheme locally of finite type over `R` which agree on `E ×_{Dₖ} X` agree on `E ×_{Dₖ} Dₖ'`
   for some `k' ⟶ k` (`AlgebraicGeometry.exists_eq_descent_of_isLimit`);
4. *(coverings)* étale morphisms `Eᵢ ⟶ V` to a quasi-compact scheme over a stage `Dₖ` which
   are jointly surjective after base change to `X` are jointly surjective after base change to
   every late enough stage (`AlgebraicGeometry.exists_forall_mem_range_of_isLimit`).

The descent of étale objects is stated in the local form in which it is used: global étale
schemes of finite presentation over `X` are glued from such local pieces.
(blueprint: `lem-weil-pbc-etale-finite-data-descent`) -/
theorem etale_finite_data_descent_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] {R : Scheme.{u}} (π : D ⟶ (Functor.const J).obj R) :
    (∀ {k : J} {V : Scheme.{u}} (p : V ⟶ D.obj k) [Etale p] {Z : Scheme.{u}}
      (β : Z ⟶ pullback p (c.π.app k)) [Etale β] (z : Z),
      ∃ (k' : J) (f : k' ⟶ k) (E : Scheme.{u}) (_ : IsAffine E) (q : E ⟶ D.obj k')
        (_ : Etale q) (e : E ⟶ V) (he : e ≫ p = q ≫ D.map f) (E' : Scheme.{u}) (π₁ : E' ⟶ E)
        (π₂ : E' ⟶ c.pt) (hπ : IsPullback π₁ π₂ q (c.π.app k')) (γ : E' ⟶ Z)
        (_ : IsOpenImmersion γ),
        γ ≫ β = pullback.lift (π₁ ≫ e) π₂
          (by rw [Category.assoc, he, reassoc_of% hπ.w, c.w f]) ∧ z ∈ Set.range γ) ∧
    (∀ {k : J} {E : Scheme.{u}} (q : E ⟶ D.obj k) [CompactSpace E] [QuasiSeparatedSpace E]
      {U : Scheme.{u}} (u : U ⟶ R) [LocallyOfFinitePresentation u]
      (φ : pullback q (c.π.app k) ⟶ U),
      φ ≫ u = pullback.snd q (c.π.app k) ≫ c.π.app k ≫ π.app k →
      ∃ (k' : J) (f : k' ⟶ k) (ψ : pullback q (D.map f) ⟶ U),
        ψ ≫ u = pullback.snd q (D.map f) ≫ π.app k' ∧
          pullback.map q (c.π.app k) q (D.map f) (𝟙 _) (c.π.app k') (𝟙 _) (by simp)
            (by simp) ≫ ψ = φ) ∧
    (∀ {k : J} {E : Scheme.{u}} (q : E ⟶ D.obj k) [CompactSpace E] {U : Scheme.{u}}
      (u : U ⟶ R) [LocallyOfFiniteType u] (ψ₁ ψ₂ : E ⟶ U),
      ψ₁ ≫ u = q ≫ π.app k → ψ₂ ≫ u = q ≫ π.app k →
      pullback.fst q (c.π.app k) ≫ ψ₁ = pullback.fst q (c.π.app k) ≫ ψ₂ →
      ∃ (k' : J) (f : k' ⟶ k), pullback.fst q (D.map f) ≫ ψ₁ = pullback.fst q (D.map f) ≫ ψ₂) ∧
    (∀ {k : J} {V : Scheme.{u}} (p : V ⟶ D.obj k) [CompactSpace V] {ι : Type u}
      {E : ι → Scheme.{u}} (e : ∀ i, E i ⟶ V) [∀ i, Etale (e i)],
      (∀ x : ↥(pullback p (c.π.app k)), ∃ i, pullback.fst p (c.π.app k) x ∈ Set.range (e i)) →
      ∃ (k' : J) (f : k' ⟶ k), ∀ (k'' : J) (g : k'' ⟶ k') (x : ↥(pullback p (D.map (g ≫ f)))),
        ∃ i, pullback.fst p (D.map (g ≫ f)) x ∈ Set.range (e i)) :=
  ⟨fun p _ _ β _ z ↦ exists_etale_refinement_of_isLimit D c hc p β z,
    fun q _ _ _ u _ φ hφ ↦ exists_hom_descent_of_isLimit D c hc π q u φ hφ,
    fun q _ _ u _ ψ₁ ψ₂ h₁ h₂ h ↦ exists_eq_descent_of_isLimit D c hc π q u ψ₁ ψ₂ h₁ h₂ h,
    fun p _ _ _ e _ h ↦ exists_forall_mem_range_of_isLimit D c hc p e h⟩

end Stage

end AlgebraicGeometry
