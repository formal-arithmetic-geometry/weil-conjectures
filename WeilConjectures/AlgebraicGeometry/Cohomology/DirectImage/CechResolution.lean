/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.Topology.Sheaves.CechComparison
public import WeilConjectures.Topology.Sheaves.Cech
public import WeilConjectures.AlgebraicGeometry.Modules.StalkExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# The Čech resolution of a sheaf of modules

Let `U : ι → X.Opens` be a finite open cover of a scheme `X` and `ℱ` an `𝒪_X`-module. Write
`j_V : V ⟶ X` for the inclusion of an open. The sheafified Čech complex `Č(U, ℱ)` has in
degree `k` the module `∏_{y : Fin (k + 1) → ι} j_{U_y,*} (ℱ|_{U_y})`, where
`U_y = U (y 0) ⊓ ⋯ ⊓ U (y k)`; it is Mathlib's Čech complex
(`CategoryTheory.cechComplexFunctor`) of the presheaf `V ↦ j_{V,*} (ℱ|_V)` of `𝒪_X`-modules.

## Main results

- `AlgebraicGeometry.Scheme.Modules.cechResolution`: the complex `Č(U, ℱ)`, and its
  augmentation `AlgebraicGeometry.Scheme.Modules.cechResolutionι : ℱ ⟶ Č(U, ℱ)`.
- `AlgebraicGeometry.Scheme.Modules.quasiIso_cechResolutionι`: the augmented Čech complex
  `0 ⟶ ℱ ⟶ Č⁰(U, ℱ) ⟶ Č¹(U, ℱ) ⟶ ⋯` is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section ExtendRestrict

lemma ι_image_preimage (V T : X.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ T = V ⊓ T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma ι_image_preimage_mono {V W : X.Opens} (h : W ≤ V) (T : X.Opens) :
    W.ι ''ᵁ W.ι ⁻¹ᵁ T ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ T := by
  rw [ι_image_preimage, ι_image_preimage]
  exact inf_le_inf_right T h

/-- The functor `ℱ ↦ j_* (ℱ|_V)` for the inclusion `j : V ⟶ X` of an open `V`. -/
noncomputable abbrev extendRestrictFunctor (V : X.Opens) : X.Modules ⥤ X.Modules :=
  restrictFunctor V.ι ⋙ pushforward V.ι

/-- The restriction `j_{V,*} (ℱ|_V) ⟶ j_{W,*} (ℱ|_W)` for opens `W ≤ V`. -/
noncomputable def extendRestrictMap {V W : X.Opens} (h : W ≤ V) :
    extendRestrictFunctor V ⟶ extendRestrictFunctor W :=
  let a : restrictFunctor V.ι ⋙ pushforward V.ι ⟶
      (restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h)) ⋙
        (pushforward (X.homOfLE h) ⋙ pushforward V.ι) :=
    Functor.whiskerLeft (restrictFunctor V.ι)
      (Functor.whiskerRight (restrictAdjunction (X.homOfLE h)).unit (pushforward V.ι))
  let b : (restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h)) ⋙
      (pushforward (X.homOfLE h) ⋙ pushforward V.ι) ⟶
        restrictFunctor (X.homOfLE h ≫ V.ι) ⋙ pushforward (X.homOfLE h ≫ V.ι) :=
    (restrictFunctorComp (X.homOfLE h) V.ι).inv ◫ (pushforwardComp (X.homOfLE h) V.ι).hom
  let c : restrictFunctor (X.homOfLE h ≫ V.ι) ⋙ pushforward (X.homOfLE h ≫ V.ι) ⟶
      restrictFunctor W.ι ⋙ pushforward W.ι :=
    (restrictFunctorCongr (X.homOfLE_ι h)).hom ◫ (pushforwardCongr (X.homOfLE_ι h)).hom
  a ≫ b ≫ c

lemma extendRestrictMap_app_app {V W : X.Opens} (h : W ≤ V) (ℱ : X.Modules) (T : X.Opens) :
    ((extendRestrictMap h).app ℱ).app T =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono h T)).op :
        Γ(ℱ, V.ι ''ᵁ V.ι ⁻¹ᵁ T) ⟶ Γ(ℱ, W.ι ''ᵁ W.ι ⁻¹ᵁ T)) := by
  simp only [extendRestrictMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.hcomp_app, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app, restrictFunctorComp_inv_app_app,
    pushforwardCongr_hom_app_app, restrictFunctorCongr_hom_app_app, restrict_map,
    ← Functor.map_comp]
  erw [Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end ExtendRestrict

section ExactSections

/-- Morphisms of `𝒪_X`-modules commute with restriction of sections. -/
lemma Hom.app_presheaf_map_apply {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V)
    (s : Γ(M, V)) : φ.app W (M.presheaf.map i.op s) = N.presheaf.map i.op (φ.app V s) :=
  congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom
    (φ.mapPresheaf.naturality i.op))) s

/-- The sections over `W` of an `𝒪_X`-module, as an abelian group. -/
noncomputable abbrev sectionsAb (W : X.Opens) : X.Modules ⥤ Ab.{u} :=
  toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op W)

instance (W : X.Opens) : (sectionsAb W).Additive where
  map_add := rfl

/-- **Exactness from sections over small opens.** A short complex of `𝒪_X`-modules is exact if
every point has arbitrarily small open neighbourhoods over which its sections are exact. -/
theorem exact_of_exact_sectionsAb (S : ShortComplex X.Modules)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      (S.map (sectionsAb W)).Exact) : S.Exact := by
  rw [exact_iff_stalkFunctor]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.presheaf a
  have ha' : S.X₃.presheaf.germ V x hxV (S.g.app V s) = S.X₃.presheaf.germ V x hxV 0 := by
    rw [map_zero]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV S.g.mapPresheaf s).symm.trans ha
  obtain ⟨V', hxV', i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ ha'
  rw [map_zero] at e
  obtain ⟨W, hxW, hWV', hW⟩ := h x V' hxV'
  rw [ShortComplex.ab_exact_iff] at hW
  obtain ⟨t, ht⟩ := hW (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) (by
    change S.g.app W (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) = 0
    rw [Hom.app_presheaf_map_apply, show S.X₃.presheaf.map (homOfLE (hWV'.trans i₁.le)).op =
      S.X₃.presheaf.map i₁.op ≫ S.X₃.presheaf.map (homOfLE hWV').op by
        rw [← Functor.map_comp]; rfl, ConcreteCategory.comp_apply, e, map_zero])
  refine ⟨S.X₁.presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor Ab x).map S.f.mapPresheaf _ = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change S.X₂.presheaf.germ W x hxW (S.f.app W t) = _
  rw [show S.f.app W t = _ from ht, TopCat.Presheaf.germ_res_apply]

/-- **Exactness from sections over small opens**, for homological complexes. -/
theorem exactAt_of_exactAt_sectionsAb {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (i : ι)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      (((sectionsAb W).mapHomologicalComplex c).obj K).ExactAt i) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_exact_sectionsAb _ fun x V hxV ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hxV
  exact ⟨W, hxW, hWV, (HomologicalComplex.exactAt_iff _ _).mp hW⟩

end ExactSections

section Complex

variable (X) in
/-- The presheaf of functors `V ↦ (ℱ ↦ j_{V,*} (ℱ|_V))` on the opens of `X`. -/
noncomputable def extendRestrictPresheaf : X.Opensᵒᵖ ⥤ X.Modules ⥤ X.Modules where
  obj V := extendRestrictFunctor V.unop
  map i := extendRestrictMap (leOfHom i.unop)
  map_id V := NatTrans.ext (funext fun ℱ ↦ hom_ext _ _ fun T ↦ by
    rw [extendRestrictMap_app_app]
    exact ℱ.presheaf.map_id _)
  map_comp i j := NatTrans.ext (funext fun ℱ ↦ hom_ext _ _ fun T ↦ by
    rw [NatTrans.comp_app, Hom.comp_app, extendRestrictMap_app_app, extendRestrictMap_app_app,
      extendRestrictMap_app_app, ← Functor.map_comp]
    rfl)

/-- The presheaf `V ↦ j_{V,*} (ℱ|_V)` of `𝒪_X`-modules. -/
noncomputable abbrev cechPresheaf (ℱ : X.Modules) : X.Opensᵒᵖ ⥤ X.Modules :=
  (extendRestrictPresheaf X).flip.obj ℱ

lemma cechPresheaf_map_app (ℱ : X.Modules) {V W : X.Opensᵒᵖ} (i : V ⟶ W) (T : X.Opens) :
    ((cechPresheaf ℱ).map i).app T =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono (leOfHom i.unop) T)).op :
        Γ(ℱ, V.unop.ι ''ᵁ V.unop.ι ⁻¹ᵁ T) ⟶ Γ(ℱ, W.unop.ι ''ᵁ W.unop.ι ⁻¹ᵁ T)) :=
  extendRestrictMap_app_app _ ℱ T

variable {ι : Type u} (U : ι → X.Opens)

/-- The **sheafified Čech complex** `Č(U, ℱ)` of an `𝒪_X`-module `ℱ` for a family `U` of opens,
as a functor of `ℱ`: in degree `k` it is `∏_{y : Fin (k + 1) → ι} j_{U_y,*} (ℱ|_{U_y})`, with
`U_y = U (y 0) ⊓ ⋯ ⊓ U (y k)` and the alternating sum of the restrictions as differential. -/
noncomputable def cechResolutionFunctor : X.Modules ⥤ CochainComplex X.Modules ℕ :=
  (extendRestrictPresheaf X).flip ⋙ cechComplexFunctor U

/-- The sheafified Čech complex `Č(U, ℱ)`. -/
noncomputable abbrev cechResolution (ℱ : X.Modules) : CochainComplex X.Modules ℕ :=
  (cechResolutionFunctor U).obj ℱ

/-- The augmentation `ℱ ⟶ Č⁰(U, ℱ) = ∏ᵢ j_{U i,*} (ℱ|_{U i})`, the product of the units of the
restrictions. -/
noncomputable def cechResolutionAugmentation (ℱ : X.Modules) : ℱ ⟶ (cechResolution U ℱ).X 0 :=
  (restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ ≫
    cechAugmentation U isTerminalTop (cechPresheaf ℱ)

@[reassoc (attr := simp)]
lemma cechResolutionAugmentation_d (ℱ : X.Modules) :
    cechResolutionAugmentation U ℱ ≫ (cechResolution U ℱ).d 0 1 = 0 := by
  rw [cechResolutionAugmentation, Category.assoc]
  erw [cechAugmentation_d]
  rw [comp_zero]

/-- The augmentation `ℱ ⟶ Č(U, ℱ)`, as a morphism of complexes from `ℱ` in degree `0`. -/
noncomputable def cechResolutionι (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶ cechResolution U ℱ :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨cechResolutionAugmentation U ℱ, cechResolutionAugmentation_d U ℱ⟩

@[simp]
lemma cechResolutionι_f_zero (ℱ : X.Modules) :
    (cechResolutionι U ℱ).f 0 = cechResolutionAugmentation U ℱ := by
  simp [cechResolutionι, CochainComplex.fromSingle₀Equiv]

end Complex

section Exactness

/-- A complex `K` augmented by `ε : Z ⟶ K⁰` is a resolution of `Z` as soon as `ε` is a
monomorphism, `Z ⟶ K⁰ ⟶ K¹` is exact and `K` is exact in positive degrees. -/
lemma quasiIso_fromSingle₀Equiv_symm {C : Type*} [Category* C] [Abelian C] {Z : C}
    {K : CochainComplex C ℕ} (ε : Z ⟶ K.X 0) (hε : ε ≫ K.d 0 1 = 0)
    (h₀ : (ShortComplex.mk ε (K.d 0 1) hε).Exact) [Mono ε] (hK : ∀ n, K.ExactAt (n + 1)) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv K Z).symm ⟨ε, hε⟩) := ⟨fun n ↦ by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h₀, by dsimp; infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [CochainComplex.fromSingle₀Equiv]) (by simp)
    all_goals first | rfl | exact HomologicalComplex.shape _ _ _ (by simp)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact hK n
    · exact CochainComplex.exactAt_succ_single_obj _ _⟩

variable {ι : Type u} (U : ι → X.Opens) (ℱ : X.Modules)

/-- The sections over `W` of an `𝒪_X`-module, as a module over `Γ(X, W)`. -/
noncomputable abbrev sectionsModuleFunctor (W : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op W)) :=
  SheafOfModules.evaluation X.ringCatSheaf (op W)

instance (W : X.Opens) : (sectionsModuleFunctor W).Additive where
  map_add := rfl

instance (W : X.Opens) (J : Type u) :
    PreservesLimitsOfShape (Discrete J) (sectionsModuleFunctor W) :=
  inferInstanceAs
    (PreservesLimitsOfShape (Discrete J) (SheafOfModules.evaluation X.ringCatSheaf (op W)))

/-- The sections over `W` of the Čech complex: the Čech complex of the presheaf
`V ↦ Γ(W, j_{V,*} (ℱ|_V))`, with explicit cochains. -/
noncomputable def sectionsCechResolutionIso (W : X.Opens) :
    ((sectionsAb W).mapHomologicalComplex _).obj (cechResolution U ℱ) ≅
      (TopCat.Presheaf.cechComplex U).obj
        (cechPresheaf ℱ ⋙ sectionsModuleFunctor W ⋙ forget₂ _ AddCommGrpCat.{u}) :=
  ((forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex _).mapIso
      (cechComplexFunctorMapIso U (sectionsModuleFunctor W) (cechPresheaf ℱ)) ≪≫
    TopCat.Presheaf.cechComplexFunctorIso U (cechPresheaf ℱ ⋙ sectionsModuleFunctor W)

/-- Over an open `W` contained in a member of the family, the sections of the Čech complex are
exact in positive degrees. -/
lemma exactAt_sectionsAb_cechResolution {W : X.Opens} {j : ι} (hW : W ≤ U j) (n : ℕ) :
    (((sectionsAb W).mapHomologicalComplex _).obj (cechResolution U ℱ)).ExactAt (n + 1) := by
  refine (ShortComplex.exact_iff_of_iso ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).mapIso
    (sectionsCechResolutionIso U ℱ W))).mpr ?_
  refine TopCat.Presheaf.exactAt_cechComplex_of_bijective U _ (j := j) (fun k y ↦ ?_) n
  have hle : ((⨅ l, U (y l)) ⊓ U j).ι ''ᵁ ((⨅ l, U (y l)) ⊓ U j).ι ⁻¹ᵁ W ≥
      (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W := by
    rw [ι_image_preimage, ι_image_preimage, inf_assoc, inf_eq_right.mpr hW]
  have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_mono
    (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _) W)) hle
  have e : (cechPresheaf ℱ ⋙ sectionsModuleFunctor W ⋙ forget₂ _ AddCommGrpCat.{u}).map
      (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op =
      ℱ.presheaf.map (homOfLE (ι_image_preimage_mono
        (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _) W)).op :=
    cechPresheaf_map_app ℱ (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op W
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

/-- The Čech complex of a cover is exact in positive degrees. -/
theorem exactAt_cechResolution (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (cechResolution U ℱ).ExactAt (n + 1) := by
  refine exactAt_of_exactAt_sectionsAb _ _ fun x V hxV ↦ ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial : x ∈ ⨆ i, U i)
  exact ⟨V ⊓ U j, ⟨hxV, hj⟩, inf_le_left,
    exactAt_sectionsAb_cechResolution U ℱ inf_le_right n⟩

end Exactness

end AlgebraicGeometry.Scheme.Modules
