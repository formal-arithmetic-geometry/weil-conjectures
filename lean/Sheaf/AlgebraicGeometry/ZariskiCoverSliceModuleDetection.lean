/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Zariski covering and module detection on small sites and their slices

Source: Stacks Project, Tags 098B, 00VH, 00VM, 00VR, 00Y0, 04IX and 03CW
(blueprint: lem-pur-zariski-cover-slice-module-detection).

The two statements use the recorded small sites without a replacement site definition.
For an object `V`, the inverse-image open `V.hom ⁻¹ᵁ U i` is the scheme-theoretic
fibre product with `U i`; its inclusion is the pullback projection. The existing
`pullbackRestrictIsoRestrict` identifies these with Mathlib's chosen pullbacks. These
representatives make the same family explicit in the ambient site, the small site of `V.left`, and
its localized site. Rings and modules lie in the common coefficient universe `u + 1`;
the indexing universe `v` is arbitrary, including empty and infinite index sets.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem module_isZero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{v} R) :
    IsZero F ↔ ∀ V : C, Subsingleton (F.val.obj (op V)) := by
  constructor
  · intro h V
    have h' := congrArg (fun f : F ⟶ F ↦ f.val.app (op V)) ((IsZero.iff_id_eq_zero F).mp h)
    exact ModuleCat.isZero_iff_subsingleton.mp ((IsZero.iff_id_eq_zero _).mpr h')
  · intro h
    apply (IsZero.iff_id_eq_zero _).mpr
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    have := h V.unop
    ext x
    exact Subsingleton.elim _ _

private theorem module_restriction_injective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{v} R) {V : C} {I : Type*} {W : I → C}
    (f : ∀ i, W i ⟶ V) (hf : Sieve.ofArrows W f ∈ J V) :
    Function.Injective (fun x : F.val.obj (op V) ↦ fun i ↦ F.val.map (f i).op x) := by
  intro x y h
  apply F.isSheaf.isSeparated V (Sieve.ofArrows W f) hf
  intro Z g hg
  obtain ⟨i, b, rfl⟩ := Sieve.ofArrows.exists hg
  change F.val.map (b ≫ f i).op x = F.val.map (b ≫ f i).op y
  simpa only [op_comp, F.val.map_comp_apply] using
    congrArg (fun z ↦ F.val.map b.op z) (congrFun h i)

private theorem module_over_isZero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{v} R) (V : C) :
    IsZero (F.over V) ↔ ∀ W : Over V, Subsingleton (F.val.obj (op W.left)) := by
  exact module_isZero_iff (F.over V)

private theorem module_isZero_cover {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{v} R) {E : C} (e : ∀ V, V ⟶ E)
    {I : Type*} (A : I → C) (f : ∀ i, A i ⟶ E)
    (hf : Sieve.ofArrows A f ∈ J E) :
    IsZero F ↔ ∀ i, IsZero (F.over (A i)) := by
  constructor
  · intro h i
    apply (module_over_isZero_iff F (A i)).mpr
    intro W
    exact (module_isZero_iff F).mp h W.left
  · intro h
    apply (module_isZero_iff F).mpr
    intro V
    constructor
    intro x y
    apply F.isSheaf.isSeparated V _ (J.pullback_stable (e V) hf)
    intro W g hg
    obtain ⟨i, k, _⟩ := Sieve.ofArrows.exists hg
    exact ((module_over_isZero_iff F (A i)).mp (h i) (Over.mk k)).elim _ _

private theorem module_isZero_of_bot {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{v} R) (h : ∀ V, (⊥ : Sieve V) ∈ J V) : IsZero F := by
  apply (module_isZero_iff F).mpr
  intro V
  exact ⟨fun x y ↦ F.isSheaf.isSeparated V ⊥ (h V) x y (fun _ _ hf ↦ hf.elim)⟩

private theorem etale_open_cover {T : Scheme.{u}} {I : Type*}
    (V : T.Etale) (W : I → V.left.Opens) (hW : ∀ x, ∃ i, x ∈ W i) :
    Sieve.ofArrows (fun i ↦ Etale.mk ((W i).ι ≫ V.hom))
      (fun i ↦ (MorphismProperty.Over.homMk (W i).ι rfl trivial :
        Etale.mk ((W i).ι ≫ V.hom) ⟶ V)) ∈ T.smallEtaleTopology V := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  change (⋃ i, Set.range (W i).ι) = Set.univ
  simpa only [Opens.range_ι, Set.iUnion_eq_univ_iff, SetLike.mem_coe] using hW

private theorem proetale_open_cover {T : Scheme.{u}} {I : Type*}
    (V : T.ProEt) (W : I → V.left.Opens) (hW : ∀ x, ∃ i, x ∈ W i) :
    Presieve.ofArrows (fun i ↦ ProEt.mk ((W i).ι ≫ V.hom))
      (fun i ↦ (MorphismProperty.Over.homMk (W i).ι rfl trivial :
        ProEt.mk ((W i).ι ≫ V.hom) ⟶ V)) ∈ ProEt.precoverage T V := by
  rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  apply etalePrecoverage_le_proetalePrecoverage
  change Presieve.ofArrows (fun i ↦ (W i).toScheme) (fun i ↦ (W i).ι) ∈
    etalePrecoverage V.left
  exact (ofArrows_mem_precoverage_iff _).mpr
    ⟨fun x ↦ by simpa only [Opens.range_ι, SetLike.mem_coe] using hW x,
      fun i ↦ inferInstance⟩

private theorem etale_identity_cover {T : Scheme.{u}} {I : Type*}
    (W : I → T.Opens) (hW : ∀ x, ∃ i, x ∈ W i) :
    Sieve.ofArrows (fun i ↦ Etale.mk (W i).ι)
      (fun i ↦ (MorphismProperty.Over.homMk (W i).ι (Category.comp_id _) trivial :
        Etale.mk (W i).ι ⟶ Etale.mk (𝟙 T))) ∈
      T.smallEtaleTopology (Etale.mk (𝟙 T)) := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  change (⋃ i, Set.range (W i).ι) = Set.univ
  simpa only [Opens.range_ι, Set.iUnion_eq_univ_iff, SetLike.mem_coe] using hW

private theorem proetale_identity_cover {T : Scheme.{u}} {I : Type*}
    (W : I → T.Opens) (hW : ∀ x, ∃ i, x ∈ W i) :
    Presieve.ofArrows (fun i ↦ ProEt.mk (W i).ι)
      (fun i ↦ (MorphismProperty.Over.homMk (W i).ι (Category.comp_id _) trivial :
        ProEt.mk (W i).ι ⟶ ProEt.mk (𝟙 T))) ∈
      ProEt.precoverage T (ProEt.mk (𝟙 T)) := by
  rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  apply etalePrecoverage_le_proetalePrecoverage
  change Presieve.ofArrows (fun i ↦ (W i).toScheme) (fun i ↦ (W i).ι) ∈
    etalePrecoverage T
  exact (ofArrows_mem_precoverage_iff _).mpr
    ⟨fun x ↦ by simpa only [Opens.range_ι, SetLike.mem_coe] using hW x,
      fun i ↦ inferInstance⟩

/-- Zariski covers and module detection on the small etale site, including empty covers.
Source: Stacks 098B, 00VH, 00VM/00VR, 00Y0, 04IX(4) and 03CW
(blueprint: lem-pur-zariski-cover-slice-module-detection).

Proof:
1. Open immersions are etale by lem-weil-pbc-open-immersion-etale. Joint
   surjectivity makes the original family etale covering; lem-pur-etale-proetale-cover
   (098B) also makes it pro-etale covering, with its full finite affine refinement condition.
2. The base-change axiom of def-weil-pbc-sites-and-cohomology gives a cover on every V.
   By lem-weil-pbc-open-immersion-base-change, the projections identify with the
   inverse-image opens shown below, which cover V.left. Step 1 applies on that scheme.
   def-pur-localized-ringed-site tests exactly the underlying covering in the slice.
3. def-weil-sheaf-of-modules-category makes the underlying abelian presheaf a sheaf.
   Its equalizer axiom says two sections with equal restrictions to every member
   have the same amalgamation, proving injectivity of the displayed restriction map.
4. The section formula in def-pur-localized-ringed-site makes each local zero module
   force zero on all covering sections. Injectivity then makes every section zero.
   Sectionwise zero is equivalent to a zero object: all component maps are uniquely
   the zero linear maps. Conversely evaluate id_F = 0 and restrict sectionwise.
5. If T is empty, every object over it is empty. The empty family is Zariski covering
   on each such object, hence covering on both small sites and their slices by Steps 1-2.
   Its unique empty matching family has a unique amalgamation. Every section module
   is therefore zero. This proves the empty assertions and includes the case I empty.
No quasi-compactness, finite-cover, constant-ring or topos-point assumption is used. -/
theorem zariskiCoverEtaleModuleDetection (T : Scheme.{u}) {I : Type v}
    (U : I → T.Opens) (hU : ∀ x : T, ∃ i : I, x ∈ U i) :
    Sieve.ofArrows (fun i ↦ Etale.mk ((U i).ι))
      (fun i ↦ (MorphismProperty.Over.homMk (U i).ι (Category.comp_id _) trivial :
        Etale.mk ((U i).ι) ⟶ Etale.mk (𝟙 T))) ∈
          T.smallEtaleTopology (Etale.mk (𝟙 T)) ∧
    (∀ V : T.Etale,
      (Sieve.ofArrows (fun i ↦ Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom))
        (fun i ↦ (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V)) ∈ T.smallEtaleTopology V) ∧
      (Sieve.ofArrows (fun i ↦ Etale.mk ((V.hom ⁻¹ᵁ U i).ι))
        (fun i ↦ (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι (Category.comp_id _) trivial :
          Etale.mk ((V.hom ⁻¹ᵁ U i).ι) ⟶ Etale.mk (𝟙 V.left))) ∈
            V.left.smallEtaleTopology (Etale.mk (𝟙 V.left))) ∧
      (Sieve.ofArrows (fun i ↦ Over.mk (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V))
        (fun i ↦ (Over.homMk (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V) (Category.comp_id _) :
          Over.mk (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V) ⟶ Over.mk (𝟙 V))) ∈
            (T.smallEtaleTopology).over V (Over.mk (𝟙 V)))) ∧
    (∀ (O : Sheaf (T.smallEtaleTopology) CommRingCat.{u + 1})
      (F : ringedSiteModules.{u + 1}
        ((sheafCompose (T.smallEtaleTopology)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
      (∀ (i : I) (W : Over (Etale.mk ((U i).ι))),
        (F.over (Etale.mk ((U i).ι))).val.obj (op W) = F.val.obj (op W.left)) ∧
      (∀ V : T.Etale, Function.Injective
        (fun x : F.val.obj (op V) ↦ fun i : I ↦
          F.val.map (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V).op x :
          F.val.obj (op V) → ∀ i : I,
            F.val.obj (op (Etale.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom))))) ∧
      (IsZero F ↔ ∀ i : I, IsZero (F.over (Etale.mk ((U i).ι)))) ∧
      (IsZero F ↔ ∀ V : T.Etale, Subsingleton (F.val.obj (op V)))) ∧
    (IsEmpty T →
      (∀ V : T.Etale, (⊥ : Sieve V) ∈ T.smallEtaleTopology V) ∧
      (∀ (V : T.Etale) (W : V.left.Etale), (⊥ : Sieve W) ∈ V.left.smallEtaleTopology W) ∧
      (∀ (V : T.Etale) (W : Over V), (⊥ : Sieve W) ∈ (T.smallEtaleTopology).over V W) ∧
      (∀ (O : Sheaf (T.smallEtaleTopology) CommRingCat.{u + 1})
        (F : ringedSiteModules.{u + 1}
        ((sheafCompose (T.smallEtaleTopology)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)), IsZero F)) := by
  have cover (V : T.Etale) := etale_open_cover V (fun i ↦ V.hom ⁻¹ᵁ U i)
    (fun x ↦ hU (V.hom x))
  have base := etale_identity_cover U hU
  have empty_cover (S : Scheme.{u}) [IsEmpty S] (V : S.Etale) :
      (⊥ : Sieve V) ∈ S.smallEtaleTopology V := by
    have : IsEmpty V.left := ⟨fun x ↦ (inferInstance : IsEmpty S).false (V.hom x)⟩
    have h := etale_open_cover V (fun i : PEmpty.{1} ↦ i.elim)
      (fun x ↦ isEmptyElim x)
    simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact base
  · intro V
    refine ⟨cover V, ?_, ?_⟩
    · exact etale_identity_cover (fun i ↦ V.hom ⁻¹ᵁ U i)
          (fun x ↦ hU (V.hom x))
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact cover V
  · intro O F
    refine ⟨fun _ _ ↦ rfl, ?_, ?_, module_isZero_iff F⟩
    · intro V
      exact module_restriction_injective F _ (cover V)
    · apply module_isZero_cover F
        (fun V ↦ (MorphismProperty.Over.homMk V.hom (Category.comp_id _) trivial :
          V ⟶ Etale.mk (𝟙 T)))
        (fun i ↦ Etale.mk ((U i).ι))
        (fun i ↦ (MorphismProperty.Over.homMk (U i).ι (Category.comp_id _) trivial :
          Etale.mk (U i).ι ⟶ Etale.mk (𝟙 T)))
      exact base
  · intro hT
    let := hT
    refine ⟨empty_cover T, ?_, ?_, fun _ F ↦ module_isZero_of_bot F (empty_cover T)⟩
    · intro V W
      have : IsEmpty V.left := ⟨fun x ↦ hT.false (V.hom x)⟩
      exact empty_cover V.left W
    · intro V W
      rw [GrothendieckTopology.mem_over_iff, (Sieve.overEquiv W).map_bot]
      exact empty_cover T W.left


/-- Zariski covers and module detection on the small pro-etale site, including empty covers.
Source: Stacks 098B, 00VH, 00VM/00VR, 00Y0, 04IX(4) and 03CW
(blueprint: lem-pur-zariski-cover-slice-module-detection).

Proof:
1. Open immersions are etale by lem-weil-pbc-open-immersion-etale. Joint
   surjectivity makes the original family etale covering; lem-pur-etale-proetale-cover
   (098B) also makes it pro-etale covering, with its full finite affine refinement condition.
2. The base-change axiom of def-weil-pbc-sites-and-cohomology gives a cover on every V.
   By lem-weil-pbc-open-immersion-base-change, the projections identify with the
   inverse-image opens shown below, which cover V.left. Step 1 applies on that scheme.
   def-pur-localized-ringed-site tests exactly the underlying covering in the slice.
3. def-weil-sheaf-of-modules-category makes the underlying abelian presheaf a sheaf.
   Its equalizer axiom says two sections with equal restrictions to every member
   have the same amalgamation, proving injectivity of the displayed restriction map.
4. The section formula in def-pur-localized-ringed-site makes each local zero module
   force zero on all covering sections. Injectivity then makes every section zero.
   Sectionwise zero is equivalent to a zero object: all component maps are uniquely
   the zero linear maps. Conversely evaluate id_F = 0 and restrict sectionwise.
5. If T is empty, every object over it is empty. The empty family is Zariski covering
   on each such object, hence covering on both small sites and their slices by Steps 1-2.
   Its unique empty matching family has a unique amalgamation. Every section module
   is therefore zero. This proves the empty assertions and includes the case I empty.
No quasi-compactness, finite-cover, constant-ring or topos-point assumption is used. -/
theorem zariskiCoverProetaleModuleDetection (T : Scheme.{u}) {I : Type v}
    (U : I → T.Opens) (hU : ∀ x : T, ∃ i : I, x ∈ U i) :
    Presieve.ofArrows (fun i ↦ ProEt.mk ((U i).ι))
      (fun i ↦ (MorphismProperty.Over.homMk (U i).ι (Category.comp_id _) trivial :
        ProEt.mk ((U i).ι) ⟶ ProEt.mk (𝟙 T))) ∈
          ProEt.precoverage T (ProEt.mk (𝟙 T)) ∧
    (∀ V : T.ProEt,
      (Presieve.ofArrows (fun i ↦ ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom))
        (fun i ↦ (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V)) ∈ ProEt.precoverage T V) ∧
      (Presieve.ofArrows (fun i ↦ ProEt.mk ((V.hom ⁻¹ᵁ U i).ι))
        (fun i ↦ (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι (Category.comp_id _) trivial :
          ProEt.mk ((V.hom ⁻¹ᵁ U i).ι) ⟶ ProEt.mk (𝟙 V.left))) ∈
            ProEt.precoverage V.left (ProEt.mk (𝟙 V.left))) ∧
      (Sieve.ofArrows (fun i ↦ Over.mk (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V))
        (fun i ↦ (Over.homMk (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V) (Category.comp_id _) :
          Over.mk (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V) ⟶ Over.mk (𝟙 V))) ∈
            (ProEt.topology T).over V (Over.mk (𝟙 V)))) ∧
    (∀ (O : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
      (F : ringedSiteModules.{u + 1}
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
      (∀ (i : I) (W : Over (ProEt.mk ((U i).ι))),
        (F.over (ProEt.mk ((U i).ι))).val.obj (op W) = F.val.obj (op W.left)) ∧
      (∀ V : T.ProEt, Function.Injective
        (fun x : F.val.obj (op V) ↦ fun i : I ↦
          F.val.map (MorphismProperty.Over.homMk (V.hom ⁻¹ᵁ U i).ι rfl trivial :
            ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom) ⟶ V).op x :
          F.val.obj (op V) → ∀ i : I,
            F.val.obj (op (ProEt.mk ((V.hom ⁻¹ᵁ U i).ι ≫ V.hom))))) ∧
      (IsZero F ↔ ∀ i : I, IsZero (F.over (ProEt.mk ((U i).ι)))) ∧
      (IsZero F ↔ ∀ V : T.ProEt, Subsingleton (F.val.obj (op V)))) ∧
    (IsEmpty T →
      (∀ V : T.ProEt, (⊥ : Sieve V) ∈ ProEt.topology T V) ∧
      (∀ (V : T.ProEt) (W : V.left.ProEt), (⊥ : Sieve W) ∈ ProEt.topology V.left W) ∧
      (∀ (V : T.ProEt) (W : Over V), (⊥ : Sieve W) ∈ (ProEt.topology T).over V W) ∧
      (∀ (O : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
        (F : ringedSiteModules.{u + 1}
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)), IsZero F)) := by
  have cover (V : T.ProEt) := proetale_open_cover V (fun i ↦ V.hom ⁻¹ᵁ U i)
    (fun x ↦ hU (V.hom x))
  have sieve_cover (V : T.ProEt) := Precoverage.generate_mem_toGrothendieck (cover V)
  have base := proetale_identity_cover U hU
  have empty_cover (S : Scheme.{u}) [IsEmpty S] (V : S.ProEt) :
      (⊥ : Sieve V) ∈ ProEt.topology S V := by
    have : IsEmpty V.left := ⟨fun x ↦ (inferInstance : IsEmpty S).false (V.hom x)⟩
    exact ProEt.bot_mem_topology V
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact base
  · intro V
    refine ⟨cover V, ?_, ?_⟩
    · exact proetale_identity_cover (fun i ↦ V.hom ⁻¹ᵁ U i)
          (fun x ↦ hU (V.hom x))
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact sieve_cover V
  · intro O F
    refine ⟨fun _ _ ↦ rfl, ?_, ?_, module_isZero_iff F⟩
    · intro V
      exact module_restriction_injective F _ (sieve_cover V)
    · apply module_isZero_cover F
        (fun V ↦ (MorphismProperty.Over.homMk V.hom (Category.comp_id _) trivial :
          V ⟶ ProEt.mk (𝟙 T)))
        (fun i ↦ ProEt.mk ((U i).ι))
        (fun i ↦ (MorphismProperty.Over.homMk (U i).ι (Category.comp_id _) trivial :
          ProEt.mk (U i).ι ⟶ ProEt.mk (𝟙 T)))
      exact Precoverage.generate_mem_toGrothendieck base
  · intro hT
    let := hT
    refine ⟨empty_cover T, ?_, ?_, fun _ F ↦ module_isZero_of_bot F (empty_cover T)⟩
    · intro V W
      have : IsEmpty V.left := ⟨fun x ↦ hT.false (V.hom x)⟩
      exact empty_cover V.left W
    · intro V W
      rw [GrothendieckTopology.mem_over_iff, (Sieve.overEquiv W).map_bot]
      exact empty_cover T W.left

end AlgebraicGeometry.Scheme
