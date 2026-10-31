/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.LineProjFractionChartData
import WeilConjectures.TraceFormula.LineProjFractionCoefficientHom
import WeilConjectures.TraceFormula.LineProjGenerationLocus
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Overlap and affine-base compatibility of fraction charts -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem lineProj_image_restrict {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    {U V : T.Opens} (h : U ≤ V) (n : ℕ) (a : Γ(A.piece n, V)) :
    lineProjImage f A L ψ U n ((A.piece n).presheaf.map (homOfLE h).op a) =
      (L.tensorPow n).presheaf.map (homOfLE (f.preimage_mono h)).op
        (lineProjImage f A L ψ V n a) := by
  let F := (tensorPullbackSectionAdjunction f).unit.app (A.piece n) ≫
    (pushforward f).map (ψ n)
  have hF (B : T.Opens) (b : Γ(A.piece n, B)) :
      F.app B b = lineProjImage f A L ψ B n b := by
    change (ψ n).app _ (((tensorPullbackSectionAdjunction f).unit.app _).app B b) = _
    exact congrArg ((ψ n).app (f ⁻¹ᵁ B))
      ((Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1
        (A.piece n) B b)
  rw [← hF, ← hF]
  exact Hom.app_presheaf_map F (homOfLE h) a

private theorem lineProj_element_restrict {T : Scheme.{u}} (A : RelativeProjAlgebra T)
    {C V : T.affineOpens} (h : C ≤ V) (n : ℕ) (a : Γ(A.piece n, V.1)) :
    (lineProjElement A C n (lineProjRestrict A h n a)).val =
      A.gradeRestriction h (lineProjElement A V n a).val := by
  exact Hom.app_presheaf_map (Sigma.ι A.piece n ≫ A.decomposition.hom)
    (homOfLE h) a

private theorem lineProj_open_restrict {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    {C V : T.affineOpens} (h : C ≤ V) (d : ℕ) (a : Γ(A.piece d, V.1)) :
    lineProjGeneratorOpen f A L ψ C d (lineProjRestrict A h d a) =
      lineProjGeneratorOpen f A L ψ V d a ⊓ (f ⁻¹ᵁ C.1) := by
  ext x
  change (x ∈ lineProjGeneratorOpen f A L ψ C d (lineProjRestrict A h d a)) ↔
    (x ∈ lineProjGeneratorOpen f A L ψ V d a) ∧ x ∈ f ⁻¹ᵁ C.1
  rw [lineProj_generator_stalk, lineProj_generator_stalk]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨⟨f.preimage_mono h hx, ?_⟩, hx⟩
    rw [lineProjRestrict, lineProj_image_restrict] at hs
    simpa only [TopCat.Presheaf.germ_res_apply] using hs
  · rintro ⟨⟨hx, hs⟩, hxC⟩
    refine ⟨hxC, ?_⟩
    rw [lineProjRestrict, lineProj_image_restrict]
    simpa only [TopCat.Presheaf.germ_res_apply] using hs

private theorem lineProj_unit_fraction_chart {R : Type u} [CommRing R]
    {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}
    (φ : R →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    {t : R} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) (hu : IsUnit (φ t)) :
    ∃ r : X ⟶ Spec (.of (HomogeneousLocalization.Away 𝒜 t)),
      r ≫ Proj.awayι 𝒜 t ht hd = Proj.fromOfGlobalSections 𝒜 φ hf ∧
      ∀ (m : ℕ) (b : R) (hb : b ∈ 𝒜 (m • d)),
        ((Scheme.ΓSpecIso _).inv ≫ r.appTop)
          (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) * φ t ^ m = φ b := by
  have hbo : X.basicOpen (φ t) = ⊤ := X.basicOpen_of_isUnit hu
  have hι : IsIso (X.basicOpen (φ t)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      ((Scheme.Opens.opensRange_ι _).trans hbo)
  have hxle : Submonoid.powers t ≤ (Submonoid.powers (φ t)).comap φ :=
    Submonoid.powers_le.mpr (Submonoid.mem_powers _)
  let F := IsLocalization.map (S := Localization.Away t) (Localization.Away (φ t)) φ hxle
  let Θ := F.comp (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t))
  let r := inv (X.basicOpen (φ t)).ι ≫ X.toSpecAway (φ t) ≫
    Spec.map (CommRingCat.ofHom Θ)
  refine ⟨r, ?_, ?_⟩
  · have key : X.toSpecAway (φ t) ≫ Spec.map (CommRingCat.ofHom Θ) =
        Proj.toBasicOpenOfGlobalSections 𝒜 φ rfl hd ht ≫
          (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom := by
      rw [Proj.toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 φ rfl hd ht hxle,
        Scheme.toSpecAway, Category.assoc]
    have hbi : (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom ≫ Proj.awayι 𝒜 t ht hd =
        (Proj.basicOpen 𝒜 t).ι := by
      rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    dsimp only [r]
    rw [Category.assoc, key, Category.assoc, hbi,
      ← Proj.ι_comp_fromOfGlobalSections 𝒜 φ hf hd ht, IsIso.inv_hom_id_assoc]
  · intro m b hb
    let K : CommRingCat.of (Localization.Away (φ t)) ⟶ Γ(X, ⊤) :=
      (Scheme.ΓSpecIso _).inv ≫ (X.toSpecAway (φ t)).appTop ≫
        (inv (X.basicOpen (φ t)).ι).appTop
    have hK : CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (φ t))) ≫ K =
        𝟙 _ := by
      have e := Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (φ t))))
      have e3 : inv (X.basicOpen (φ t)).ι ≫ X.toSpecAway (φ t) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, ⊤) (Localization.Away (φ t)))) = X.toSpecΓ := by
        rw [Scheme.toSpecAway_SpecMap_algebraMap, IsIso.inv_hom_id_assoc]
      dsimp only [K]
      rw [reassoc_of% e, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        Category.assoc, e3, Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id
    have hscalar : (Scheme.ΓSpecIso _).inv ≫ r.appTop = CommRingCat.ofHom Θ ≫ K := by
      dsimp only [r, K]
      simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [← reassoc_of% (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom Θ))]
    have hmk : Θ (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) *
        algebraMap Γ(X, ⊤) (Localization.Away (φ t)) (φ t) ^ m =
          algebraMap Γ(X, ⊤) (Localization.Away (φ t)) (φ b) := by
      have h := IsLocalization.mk'_spec (S := Localization.Away t) b
        (⟨t ^ m, m, rfl⟩ : Submonoid.powers t)
      have hh := congrArg F h
      simpa only [Θ, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', map_mul, map_pow,
        F, IsLocalization.map_eq] using hh
    rw [hscalar]
    have hh := congrArg K hmk
    have hKa (c : Γ(X, ⊤)) : K (algebraMap Γ(X, ⊤) (Localization.Away (φ t)) c) = c :=
      congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) ↦ g c) hK
    change K (Θ (HomogeneousLocalization.Away.mk 𝒜 ht m b hb)) * φ t ^ m = φ b
    simpa only [map_mul, map_pow, hKa] using hh

private noncomputable def lineProj_awayMap {R S : Type u} [CommRing R] [CommRing S]
    {σ τ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    [SetLike τ S] [AddSubgroupClass τ S]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (γ : 𝒜 →+*ᵍ ℬ) (a : R) (b : S) (h : b = γ a) :
    HomogeneousLocalization.Away 𝒜 a →+* HomogeneousLocalization.Away ℬ b :=
  h.symm ▸ HomogeneousLocalization.Away.map γ a

private theorem lineProj_awayMap_mk {R S : Type u} [CommRing R] [CommRing S]
    {σ τ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    [SetLike τ S] [AddSubgroupClass τ S]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (γ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (a : R) (b : S) (h : b = γ a)
    (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d) (m : ℕ) (c : R) (c' : S)
    (hc : c ∈ 𝒜 (m • d)) (hc' : c' ∈ ℬ (m • d)) (he : c' = γ c) :
    lineProj_awayMap γ a b h (HomogeneousLocalization.Away.mk 𝒜 ha m c hc) =
      HomogeneousLocalization.Away.mk ℬ hb m c' hc' := by
  subst b c'
  exact HomogeneousLocalization.Away.map_mk γ a ha m c hc

private theorem lineProj_awayMap_chart {R S : Type u} [CommRing R] [CommRing S]
    {σ τ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    [SetLike τ S] [AddSubgroupClass τ S]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (γ : 𝒜 →+*ᵍ ℬ)
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map γ)
    {d : ℕ} (hd : 0 < d) (a : R) (b : S) (h : b = γ a)
    (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d) :
    Proj.awayι ℬ b hb hd ≫ Proj.map γ hirr =
      Spec.map (CommRingCat.ofHom (lineProj_awayMap γ a b h)) ≫ Proj.awayι 𝒜 a ha hd := by
  subst b
  exact Proj.awayι_comp_map γ hirr hd a ha

private theorem lineProj_fraction_base {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (q : ∀ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
      LineProjChart f A L ψ V d a)
    (hq : ∀ (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)),
      LineProjFractionFormula f A L ψ V d a
        (lineProjGeneratorOpen f A L ψ V d a) inf_le_left (q V d hd a)) :
    LineProjBaseRefinement f A L ψ q := by
  intro V C h d hd a
  refine ⟨lineProj_open_restrict f A L ψ h d a, ?_⟩
  intro hG
  let aC := lineProjRestrict A h d a
  let γ := A.gradeRestriction h
  let av := (lineProjElement A V d a).val
  let ac := (lineProjElement A C d aC).val
  have hac : ac = γ av := lineProj_element_restrict A h d a
  let ℓ : HomogeneousLocalization.Away (A.grade V) av →+*
      HomogeneousLocalization.Away (A.grade C) ac :=
    lineProj_awayMap (𝒜 := A.grade V) (ℬ := A.grade C) γ av ac hac
  let G := lineProjGeneratorOpen f A L ψ C d aC
  let r := q C d hd aC ≫ Spec.map (CommRingCat.ofHom ℓ)
  have hr : LineProjFractionFormula f A L ψ V d a G (hG.trans inf_le_left) r := by
    intro m b
    have hscalar : lineProjScalar G r = CommRingCat.ofHom ℓ ≫
        lineProjScalar G (q C d hd aC) := by
      dsimp only [r, lineProjScalar]
      simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [← reassoc_of% (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ℓ))]
    have hℓ : ℓ (HomogeneousLocalization.Away.mk (A.grade V)
        (lineProjElement A V d a).property m
        (lineProjElement A V (m • d) b).val
        (lineProjElement A V (m • d) b).property) =
        HomogeneousLocalization.Away.mk (A.grade C)
          (lineProjElement A C d aC).property m
          (lineProjElement A C (m • d) (lineProjRestrict A h (m • d) b)).val
          (lineProjElement A C (m • d) (lineProjRestrict A h (m • d) b)).property := by
      exact lineProj_awayMap_mk γ av ac hac _ _ m _ _ _ _
        (lineProj_element_restrict A h (m • d) b)
    rw [hscalar]
    change lineProjScalar G (q C d hd aC) (ℓ _) • _ = _
    rw [hℓ]
    have hh := hq C d hd aC m (lineProjRestrict A h (m • d) b)
    dsimp only [LineProjFractionFormula] at hh
    dsimp only [aC] at hh
    simp only [lineProjRestrict, lineProj_image_restrict] at hh
    dsimp only [G, aC, lineProjRestrict] at *
    simpa only [presheaf_map_homOfLE_map_homOfLE] using hh
  have heq : W.homOfLE hG ≫ q V d hd a = r :=
    (lineProj_fraction_unique f A L ψ V d a G hG _ _
      (lineProj_fraction_restrict f A L ψ V d a _ G inf_le_left hG _ (hq V d hd a)) hr)
  have htrans : (A.gradeIso C).inv ≫ A.localTransition h ≫ (A.gradeIso V).hom =
      Proj.map γ (A.affineData.irrelevant_le_map_res h) := by
    rw [← A.gradeIso_naturality h, Iso.inv_hom_id_assoc]
    rfl
  unfold lineProjChartToLocal
  rw [Category.assoc, htrans]
  have haway : Proj.awayι (A.grade C) ac (lineProjElement A C d aC).property hd ≫
        Proj.map γ (A.affineData.irrelevant_le_map_res h) =
      Spec.map (CommRingCat.ofHom ℓ) ≫
        Proj.awayι (A.grade V) av (lineProjElement A V d a).property hd := by
    exact lineProj_awayMap_chart γ _ hd av ac hac _ _
  rw [haway]
  simpa only [r, aC, Category.assoc] using
    congrArg (fun z ↦ z ≫ Proj.awayι (A.grade V) av
      (lineProjElement A V d a).property hd) heq

private theorem lineProj_chart_in_frame {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (B : W.Opens) (hB : B ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B)) (he : IsFreeGenerator e)
    (φ : A.sections V →+* Γ(W, B))
    (hφ : ∀ (n : ℕ) (b : Γ(A.piece n, V.1)),
      φ (lineProjElement A V n b).val • lineProjFramePower L B e n =
        (L.tensorPow n).presheaf.map (homOfLE hB).op (lineProjImage f A L ψ V.1 n b))
    (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1))
    (hBa : B ≤ lineProjGeneratorOpen f A L ψ V d a)
    (q : LineProjChart f A L ψ V d a)
    (hq : LineProjFractionFormula f A L ψ V d a
      (lineProjGeneratorOpen f A L ψ V d a) inf_le_left q) :
    ∃ (hf : (HomogeneousIdeal.irrelevant (A.grade V)).toIdeal.map
        (B.topIso.inv.hom.comp φ) = ⊤),
      W.homOfLE hBa ≫ lineProjChartToLocal f A L ψ V d hd a q =
        Proj.fromOfGlobalSections (A.grade V) (B.topIso.inv.hom.comp φ) hf := by
  let ca := φ (lineProjElement A V d a).val
  have hs : IsFreeGenerator (ca • lineProjFramePower L B e d) := by
    rw [hφ]
    simpa only [presheaf_map_homOfLE_map_homOfLE] using
      (lineProj_chart_generator f A L ψ V d a).map hBa
  obtain ⟨u, hu⟩ := (lineProj_frame_generator L B e he d).exists_unit_smul_eq hs
  have hca : IsUnit ca :=
    ((lineProj_frame_generator L B e he d).smul_left_injective hu).symm ▸ u.isUnit
  let Φ := B.topIso.inv.hom.comp φ
  have hΦ : IsUnit (Φ (lineProjElement A V d a).val) := hca.map B.topIso.inv.hom
  have hf : (HomogeneousIdeal.irrelevant (A.grade V)).toIdeal.map Φ = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem Φ
      (HomogeneousIdeal.mem_irrelevant_of_mem _ hd (lineProjElement A V d a).property)) hΦ
  obtain ⟨r, hr, hfrac⟩ := lineProj_unit_fraction_chart (A.grade V) Φ hf hd
    (lineProjElement A V d a).property hΦ
  have hrform : LineProjFractionFormula f A L ψ V d a B hB r := by
    intro m b
    have hnum := hφ (m • d) b
    have hden := hφ d a
    rw [← hden, lineProj_power_smul, lineProj_power_frame, smul_smul]
    rw [← hnum]
    congr 1
    have hh := congrArg B.topIso.hom (hfrac m (lineProjElement A V (m • d) b).val
      (lineProjElement A V (m • d) b).property)
    simpa only [map_mul, map_pow, lineProjScalar, Φ, RingHom.comp_apply,
      ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
      Category.assoc] using hh
  have heq := lineProj_fraction_unique f A L ψ V d a B hBa _ _
    (lineProj_fraction_restrict f A L ψ V d a _ B inf_le_left hBa q hq) hrform
  refine ⟨hf, ?_⟩
  change W.homOfLE hBa ≫ q ≫ _ = _
  rw [← Category.assoc, heq, hr]

private theorem lineProj_hom_ext {W Y : Scheme.{u}} (G : W.Opens)
    (f g : G.toScheme ⟶ Y)
    (h : ∀ (x : W), x ∈ G → ∃ (B : W.Opens) (hB : B ≤ G), x ∈ B ∧
      W.homOfLE hB ≫ f = W.homOfLE hB ≫ g) : f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨B, hB, hxB, heq⟩ := h x.val x.property
  let j := W.homOfLE hB
  refine ⟨j.opensRange, ?_, ?_⟩
  · refine ⟨⟨x.val, hxB⟩, ?_⟩
    apply Subtype.ext
    exact W.homOfLE_apply hB _
  · apply (cancel_epi j.isoOpensRange.hom).mp
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι] using heq

private theorem lineProj_same_base {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V))
        (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (V : T.affineOpens) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (a : Γ(A.piece d, V.1)) (b : Γ(A.piece e, V.1))
    (qa : LineProjChart f A L ψ V d a) (qb : LineProjChart f A L ψ V e b)
    (ha : LineProjFractionFormula f A L ψ V d a
      (lineProjGeneratorOpen f A L ψ V d a) inf_le_left qa)
    (hb : LineProjFractionFormula f A L ψ V e b
      (lineProjGeneratorOpen f A L ψ V e b) inf_le_left qb) :
    W.homOfLE (inf_le_left :
        lineProjGeneratorOpen f A L ψ V d a ⊓ lineProjGeneratorOpen f A L ψ V e b ≤
          lineProjGeneratorOpen f A L ψ V d a) ≫
        lineProjChartToLocal f A L ψ V d hd a qa =
      W.homOfLE inf_le_right ≫ lineProjChartToLocal f A L ψ V e he b qb := by
  apply lineProj_hom_ext
  intro x hx
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨B, hxB, hBG, v, hv⟩ := exists_isFreeGenerator L hx
  have hBa : B.1 ≤ lineProjGeneratorOpen f A L ψ V d a := hBG.trans inf_le_left
  have hBb : B.1 ≤ lineProjGeneratorOpen f A L ψ V e b := hBG.trans inf_le_right
  have hB : B.1 ≤ f ⁻¹ᵁ V.1 := hBa.trans inf_le_left
  obtain ⟨φ, hφ⟩ := lineProj_local_coefficient_hom f A L ψ hunit hmul V B.1 hB v hv
  obtain ⟨hf, hfa⟩ := lineProj_chart_in_frame f A L ψ V B.1 hB v hv φ hφ d hd a hBa qa ha
  obtain ⟨hf', hfb⟩ := lineProj_chart_in_frame f A L ψ V B.1 hB v hv φ hφ e he b hBb qb hb
  refine ⟨B.1, hBG, hxB, ?_⟩
  simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using hfa.trans hfb.symm

private theorem lineProj_base_relative {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (q : ∀ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
      LineProjChart f A L ψ V d a)
    (hbase : LineProjBaseRefinement f A L ψ q)
    (V C : T.affineOpens) (h : C ≤ V) (d : ℕ) (hd : 0 < d)
    (a : Γ(A.piece d, V.1)) (B : W.Opens)
    (hB : B ≤ lineProjGeneratorOpen f A L ψ C d (lineProjRestrict A h d a))
    (hBV : B ≤ lineProjGeneratorOpen f A L ψ V d a) :
    W.homOfLE hBV ≫ lineProjChartToRelative f A L ψ V d hd a (q V d hd a) =
      W.homOfLE hB ≫ lineProjChartToRelative f A L ψ C d hd
        (lineProjRestrict A h d a) (q C d hd (lineProjRestrict A h d a)) := by
  obtain ⟨hopen, hchart⟩ := hbase V C h d hd a
  have hG : lineProjGeneratorOpen f A L ψ C d (lineProjRestrict A h d a) ≤
      lineProjGeneratorOpen f A L ψ V d a := by rw [hopen]; exact inf_le_left
  have htrans : (A.gradeIso C).inv ≫ A.localTransition h ≫ (A.gradeIso V).hom =
      A.affineData.relProjFunctor.map (homOfLE h) := by
    rw [← A.gradeIso_naturality h, Iso.inv_hom_id_assoc]
  have heq := congrArg (fun z ↦ W.homOfLE hB ≫ z ≫ A.affineData.relProjι V)
    (hchart hG)
  simpa only [lineProjChartToRelative, Category.assoc, Scheme.homOfLE_homOfLE_assoc,
    htrans, Scheme.GradedAlgebraData.relProjFunctor_map_relProjι] using heq

/-- Fraction equations force the relative-Proj charts to agree and respect affine bases.

Source: Stacks Project, Constructions, Tags 01NK (uniqueness on overlaps), 01M4
(standard Proj opens), and 01O9 (affine-base gluing).
(blueprint: lem-trf-line-proj-fraction-compatibility).

Proof: In a local frame e of L over B inside f^{-1}V, take the unique coefficient
of each homogeneous image in e^n. The unit and multiplication laws define a ring map
phi:A(V) to O(B). If psi(a) generates, phi(a) is a unit. Mathlib's morphism from global
sections to Proj therefore factors through D_+(a), with scalar formula
rho(b/a^m) phi(a)^m=phi(b). Tensor-power cancellation and fraction uniqueness identify
this factorization with the restriction of q_a. Thus all charts over V agree locally
with the same Proj morphism and agree on arbitrary-degree overlaps.
For an affine inclusion C into V, naturality of the normalized pullback adjunction and
psi identifies the restricted image sections. Their basis-germ criteria identify the
restricted generator open with G_a intersect f^{-1}C. The graded restriction map
A(V) to A(C) induces the homogeneous-localization map sending b/a^m to b|C/(a|C)^m.
Compose q_{C,a|C} with its Spec map. Its fraction equation, transported by the section
restriction identities, is the fraction equation for q_{V,a} on the smaller open.
Uniqueness proves equality; the standard away-chart naturality theorem proves the
asserted local Proj transition, and gradeIso_naturality rewrites its required form.
Finally around any point of an arbitrary-base overlap choose an affine C inside V
intersect V'. Base refinement reduces both maps to charts over C, where the same-base
argument applies. Scheme morphisms agree locally, so they agree on the whole overlap.
The argument allows empty opens, zero divisors, and exponent zero. -/
theorem lineProj_fraction_compatibility {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V))
        (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (q : ∀ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
      LineProjChart f A L ψ V d a)
    (hq : ∀ (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)),
      LineProjFractionFormula f A L ψ V d a
        (lineProjGeneratorOpen f A L ψ V d a) inf_le_left (q V d hd a)) :
    (∀ (V V' : T.affineOpens) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
        (a : Γ(A.piece d, V.1)) (b : Γ(A.piece e, V'.1)),
        W.homOfLE (inf_le_left :
            lineProjGeneratorOpen f A L ψ V d a ⊓ lineProjGeneratorOpen f A L ψ V' e b ≤
              lineProjGeneratorOpen f A L ψ V d a) ≫
            lineProjChartToRelative f A L ψ V d hd a (q V d hd a) =
          W.homOfLE inf_le_right ≫
            lineProjChartToRelative f A L ψ V' e he b (q V' e he b)) ∧
      LineProjBaseRefinement f A L ψ q := by
  classical
  have hbase := lineProj_fraction_base f A L ψ q hq
  refine ⟨?_, hbase⟩
  intro V V' d e hd he a b
  apply lineProj_hom_ext
  intro x hx
  obtain ⟨C₀, hC₀, hxC, hCVV⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ V.1 ⊓ V'.1 from
      ⟨(inf_le_left : lineProjGeneratorOpen f A L ψ V d a ≤ _) hx.1,
        (inf_le_left : lineProjGeneratorOpen f A L ψ V' e b ≤ _) hx.2⟩)
  let C : T.affineOpens := ⟨C₀, hC₀⟩
  have hCV : C ≤ V := hCVV.trans inf_le_left
  have hCV' : C ≤ V' := hCVV.trans inf_le_right
  let H := lineProjGeneratorOpen f A L ψ V d a ⊓
    lineProjGeneratorOpen f A L ψ V' e b
  let B := H ⊓ (f ⁻¹ᵁ C.1)
  let aC := lineProjRestrict A hCV d a
  let bC := lineProjRestrict A hCV' e b
  have hBa : B ≤ lineProjGeneratorOpen f A L ψ V d a := inf_le_left.trans inf_le_left
  have hBb : B ≤ lineProjGeneratorOpen f A L ψ V' e b := inf_le_left.trans inf_le_right
  have hBaC : B ≤ lineProjGeneratorOpen f A L ψ C d aC := by
    rw [(hbase V C hCV d hd a).1]
    exact le_inf hBa inf_le_right
  have hBbC : B ≤ lineProjGeneratorOpen f A L ψ C e bC := by
    rw [(hbase V' C hCV' e he b).1]
    exact le_inf hBb inf_le_right
  have hsa := lineProj_base_relative f A L ψ q hbase V C hCV d hd a B hBaC hBa
  have hsb := lineProj_base_relative f A L ψ q hbase V' C hCV' e he b B hBbC hBb
  have hs := lineProj_same_base f A L ψ hunit hmul C d e hd he aC bC
    (q C d hd aC) (q C e he bC) (hq C d hd aC) (hq C e he bC)
  have hsame := congrArg (fun z ↦ W.homOfLE (le_inf hBaC hBbC) ≫ z ≫
    A.affineData.relProjι C) hs
  have hsame' : W.homOfLE hBaC ≫ lineProjChartToRelative f A L ψ C d hd aC
        (q C d hd aC) = W.homOfLE hBbC ≫
      lineProjChartToRelative f A L ψ C e he bC (q C e he bC) := by
    simpa only [lineProjChartToRelative, Category.assoc,
      Scheme.homOfLE_homOfLE_assoc] using hsame
  refine ⟨B, inf_le_left, ⟨hx, hxC⟩, ?_⟩
  simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using
    hsa.trans (hsame'.trans hsb.symm)

end AlgebraicGeometry.Scheme.Modules
