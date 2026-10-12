/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Topology.Sheaves.Cech

/-!
# The sheafified Čech complex

Let `X` be a scheme, `V : ι → X.Opens` a finite family of opens and `ℱ` an `𝒪_X`-module. For an
open `U` of `X` write `ℱ_U = j_* (ℱ|_U)` for `j : U ⟶ X` the inclusion
(`AlgebraicGeometry.Scheme.Modules.extendRestrict`): its sections over `W` are `Γ(ℱ, U ⊓ W)`.
The **sheafified Čech complex** `𝒞(V, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.cechSheafComplex`) has in degree `k` the module
`⨁_{y : Fin (k + 1) → ι} ℱ_{V (y 0) ⊓ ⋯ ⊓ V (y k)}` and the alternating sum of the restrictions
as differential. Its sections over an open `W` form the Čech complex of the family `W ⊓ V i`
(`AlgebraicGeometry.Scheme.Modules.cechSheafSectionsIso`). If the `V i` cover `X`, the
augmentation `ℱ ⟶ 𝒞⁰(V, ℱ)` makes `𝒞(V, ℱ)` a resolution of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.quasiIso_cechSheafι`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Sections

variable (W : X.Opens)

/-- The sections functor `M ↦ Γ(M, W)`, with values in abelian groups. -/
noncomputable def sectionsFunctor : X.Modules ⥤ Ab.{u} :=
  Modules.toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op W)

instance : (sectionsFunctor W).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (sectionsFunctor W) :=
  have : PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙
      forget₂ (ModuleCat Γ(X, W)) Ab) := comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_natIso (Iso.refl _ :
    SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙ forget₂ (ModuleCat Γ(X, W)) Ab ≅
      sectionsFunctor W)

@[simp]
lemma sectionsFunctor_obj (M : X.Modules) : (sectionsFunctor W).obj M = Γ(M, W) := rfl

@[simp]
lemma sectionsFunctor_map {M N : X.Modules} (φ : M ⟶ N) :
    (sectionsFunctor W).map φ = φ.app W := rfl

/-- A morphism of `𝒪_X`-modules which is injective on all sections is a monomorphism. -/
lemma mono_of_injective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ W : X.Opens, Function.Injective (φ.app W)) : Mono φ := by
  have : Mono ((Modules.toPresheaf X).map φ) := by
    have (W : (X.Opens)ᵒᵖ) : Mono (((Modules.toPresheaf X).map φ).app W) :=
      (AddCommGrpCat.mono_iff_injective _).2 (h W.unop)
    exact NatTrans.mono_of_mono_app _
  exact (Modules.toPresheaf X).mono_of_mono_map this

/-- The sections of a monomorphism of `𝒪_X`-modules are injective. -/
lemma injective_app_of_mono' {M N : X.Modules} (φ : M ⟶ N) [Mono φ] :
    Function.Injective (φ.app W) := by
  have : Mono ((sectionsFunctor W).map φ) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- **Exactness from sections.** A short complex of `𝒪_X`-modules is exact as soon as, near every
point of every open `W`, there are arbitrarily small opens on which its sections form an exact
sequence. -/
lemma ShortComplex.exact_of_exact_sectionsFunctor (S : ShortComplex X.Modules)
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ (V : X.Opens) (_ : V ≤ W), x ∈ V ∧
      (S.map (sectionsFunctor V)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  refine epi_of_forall_exists_app_eq _ fun W t x hx ↦ ?_
  obtain ⟨V, hVW, hxV, hV⟩ := h W x hx
  rw [ShortComplex.ab_exact_iff] at hV
  let z : Γ(S.X₂, V) := S.iCycles.app V (S.cycles.presheaf.map (homOfLE hVW).op t)
  have hz : S.g.app V z = 0 := by
    change (S.iCycles ≫ S.g).app V _ = 0
    rw [S.iCycles_g, Hom.zero_app]
    rfl
  obtain ⟨s, hs⟩ := hV z hz
  refine ⟨V, hVW, hxV, s, injective_app_of_mono' V S.iCycles ?_⟩
  change (S.toCycles ≫ S.iCycles).app V s = z
  rw [S.toCycles_i]
  exact hs

end Sections

variable (ℱ : X.Modules)

section ExtendRestrict

/-- The module `ℱ_U = j_* (ℱ|_U)` attached to an open `U` of `X`, with `j : U ⟶ X` the inclusion:
its sections over `W` are those of `ℱ` over `U ⊓ W`. -/
noncomputable abbrev extendRestrict (U : X.Opens) : X.Modules :=
  (pushforward U.ι).obj (ℱ.restrict U.ι)

lemma image_preimage_ι (U W : X.Opens) : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = U ⊓ W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma image_preimage_ι_mono {U U' : X.Opens} (h : U' ≤ U) (W : X.Opens) :
    U'.ι ''ᵁ (U'.ι ⁻¹ᵁ W) ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := by
  rw [image_preimage_ι, image_preimage_ι]
  exact inf_le_inf_right W h

lemma extendRestrict_obj (U W : X.Opens) :
    Γ(ℱ.extendRestrict U, W) = Γ(ℱ, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) := rfl

lemma extendRestrict_presheaf_map (U : X.Opens) {W W' : X.Opens} (i : W' ⟶ W) :
    (ℱ.extendRestrict U).presheaf.map i.op =
      ℱ.presheaf.map (homOfLE (image_preimage_ι_mono le_rfl W' |>.trans
        (by rw [image_preimage_ι, image_preimage_ι]; exact inf_le_inf_left U i.le))).op := rfl

lemma extendRestrict_smul (U W : X.Opens) (r : Γ(X, W)) (m : Γ(ℱ.extendRestrict U, W)) :
    r • m = (X.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op r •
      (show Γ(ℱ, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) from m) : Γ(ℱ, U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) := rfl

/-- The restriction morphism `ℱ_U ⟶ ℱ_{U'}` for `U' ≤ U`. -/
noncomputable def extendRestrictMap {U U' : X.Opens} (h : U' ≤ U) :
    ℱ.extendRestrict U ⟶ ℱ.extendRestrict U' :=
  ⟨PresheafOfModules.homMk
    { app W := ℱ.presheaf.map (homOfLE (image_preimage_ι_mono h W.unop)).op
      naturality W W' i := by
        ext m
        change ℱ.presheaf.map _ (ℱ.presheaf.map _ m) = ℱ.presheaf.map _ (ℱ.presheaf.map _ m)
        rw [presheaf_map_map_apply, presheaf_map_map_apply]
        rfl }
    fun W r m ↦ by
      change ℱ.presheaf.map _ (X.presheaf.map _ r • m) = X.presheaf.map _ r • ℱ.presheaf.map _ m
      rw [map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl⟩

lemma extendRestrictMap_app {U U' : X.Opens} (h : U' ≤ U) (W : X.Opens)
    (m : Γ(ℱ.extendRestrict U, W)) :
    (ℱ.extendRestrictMap h).app W m =
      ℱ.presheaf.map (homOfLE (image_preimage_ι_mono h W)).op m := rfl

@[simp]
lemma extendRestrictMap_self {U : X.Opens} (h : U ≤ U) :
    ℱ.extendRestrictMap h = 𝟙 _ := by
  ext W m
  rw [extendRestrictMap_app]
  exact presheaf_map_id_apply _ _ _

@[reassoc (attr := simp)]
lemma extendRestrictMap_comp {U U' U'' : X.Opens} (h : U' ≤ U) (h' : U'' ≤ U') :
    ℱ.extendRestrictMap h ≫ ℱ.extendRestrictMap h' = ℱ.extendRestrictMap (h'.trans h) := by
  ext W m
  rw [Hom.comp_app, ConcreteCategory.comp_apply, extendRestrictMap_app, extendRestrictMap_app,
    extendRestrictMap_app, presheaf_map_map_apply]
  rfl

/-- The unit `ℱ ⟶ ℱ_U`, restricting sections to `U`. -/
noncomputable def extendRestrictUnit (U : X.Opens) : ℱ ⟶ ℱ.extendRestrict U :=
  (restrictAdjunction U.ι).unit.app ℱ

lemma extendRestrictUnit_app (U W : X.Opens) (m : Γ(ℱ, W)) :
    (ℱ.extendRestrictUnit U).app W m =
      ℱ.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op m := rfl

@[reassoc (attr := simp)]
lemma extendRestrictUnit_comp_extendRestrictMap {U U' : X.Opens} (h : U' ≤ U) :
    ℱ.extendRestrictUnit U ≫ ℱ.extendRestrictMap h = ℱ.extendRestrictUnit U' := by
  ext W m
  rw [Hom.comp_app, ConcreteCategory.comp_apply, extendRestrictUnit_app, extendRestrictMap_app,
    extendRestrictUnit_app, presheaf_map_map_apply]
  rfl

end ExtendRestrict

section Cech

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → X.Opens)

/-- The term `⨁_{y : Fin (k + 1) → ι} ℱ_{V (y 0) ⊓ ⋯ ⊓ V (y k)}` of degree `k` of the sheafified
Čech complex. -/
noncomputable abbrev cechSheafX (k : ℕ) : X.Modules :=
  ⨁ fun y : Fin (k + 1) → ι ↦ ℱ.extendRestrict (⨅ l, V (y l))

/-- The map of the sheafified Čech cosimplicial object along `θ : Fin (m + 1) → Fin (n + 1)`:
the component of index `z` is the restriction of the component of index `z ∘ θ`. -/
noncomputable def cechSheafMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    cechSheafX ℱ V m ⟶ cechSheafX ℱ V n :=
  biproduct.lift fun z ↦ biproduct.π _ (z ∘ θ) ≫
    ℱ.extendRestrictMap (TopCat.Presheaf.iInf_le_iInf_comp V z θ)

@[reassoc (attr := simp)]
lemma cechSheafMap_π {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (z : Fin (n + 1) → ι) :
    cechSheafMap ℱ V θ ≫ biproduct.π _ z = biproduct.π _ (z ∘ θ) ≫
      ℱ.extendRestrictMap (TopCat.Presheaf.iInf_le_iInf_comp V z θ) :=
  biproduct.lift_π _ _

lemma cechSheafMap_id (m : ℕ) : cechSheafMap ℱ V (id : Fin (m + 1) → Fin (m + 1)) = 𝟙 _ := by
  refine biproduct.hom_ext _ _ fun z ↦ ?_
  rw [cechSheafMap_π, extendRestrictMap_self, Category.comp_id, Category.id_comp]
  rfl

lemma cechSheafMap_comp {m n p : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (θ' : Fin (n + 1) → Fin (p + 1)) :
    cechSheafMap ℱ V (θ' ∘ θ) = cechSheafMap ℱ V θ ≫ cechSheafMap ℱ V θ' := by
  refine biproduct.hom_ext _ _ fun z ↦ ?_
  rw [Category.assoc, cechSheafMap_π, cechSheafMap_π, cechSheafMap_π_assoc,
    extendRestrictMap_comp]
  rfl

/-- The sheafified Čech cosimplicial object of `ℱ` for the family `V`. -/
noncomputable def cechSheafCosimplicial : CosimplicialObject X.Modules where
  obj k := cechSheafX ℱ V k.len
  map θ := cechSheafMap ℱ V θ.toOrderHom
  map_id k := cechSheafMap_id ℱ V k.len
  map_comp θ θ' := cechSheafMap_comp ℱ V θ.toOrderHom θ'.toOrderHom

/-- The **sheafified Čech complex** `𝒞(V, ℱ)`: the alternating coface map complex of
`AlgebraicGeometry.Scheme.Modules.cechSheafCosimplicial`. -/
noncomputable def cechSheafComplex : CochainComplex X.Modules ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex X.Modules).obj (cechSheafCosimplicial ℱ V)

lemma cechSheafComplex_X (k : ℕ) : (cechSheafComplex ℱ V).X k = cechSheafX ℱ V k := rfl

lemma cechSheafComplex_d (k : ℕ) :
    (cechSheafComplex ℱ V).d k (k + 1) =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • cechSheafMap ℱ V i.succAbove :=
  CochainComplex.of_d _ _ _ k

/-- The augmentation `ℱ ⟶ 𝒞⁰(V, ℱ)`, restricting sections to the `V i`. -/
noncomputable def cechSheafAug : ℱ ⟶ cechSheafX ℱ V 0 :=
  biproduct.lift fun y ↦ ℱ.extendRestrictUnit _

@[reassoc (attr := simp)]
lemma cechSheafAug_π (y : Fin 1 → ι) :
    cechSheafAug ℱ V ≫ biproduct.π _ y = ℱ.extendRestrictUnit _ :=
  biproduct.lift_π _ _

lemma cechSheafAug_comp_cechSheafMap {n : ℕ} (θ : Fin 1 → Fin (n + 1)) :
    cechSheafAug ℱ V ≫ cechSheafMap ℱ V θ = biproduct.lift fun y ↦ ℱ.extendRestrictUnit _ := by
  refine biproduct.hom_ext _ _ fun z ↦ ?_
  rw [Category.assoc, cechSheafMap_π, cechSheafAug_π_assoc,
    extendRestrictUnit_comp_extendRestrictMap, biproduct.lift_π]

lemma cechSheafAug_d : cechSheafAug ℱ V ≫ (cechSheafComplex ℱ V).d 0 1 = 0 := by
  rw [cechSheafComplex_d, Preadditive.comp_sum, Fin.sum_univ_two]
  simp only [Preadditive.comp_zsmul, cechSheafAug_comp_cechSheafMap]
  simp

/-- The augmentation `ℱ ⟶ 𝒞(V, ℱ)`, as a morphism of complexes. -/
noncomputable def cechSheafι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ cechSheafComplex ℱ V :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨cechSheafAug ℱ V, cechSheafAug_d ℱ V⟩

end Cech

section BiproductSections

variable {J : Type*} [Fintype J] (f : J → X.Modules) (W : X.Opens)

lemma biproduct_app_eq_sum (x : Γ(⨁ f, W)) :
    x = ∑ j, (biproduct.ι f j).app W ((biproduct.π f j).app W x) := by
  conv_lhs => rw [← ConcreteCategory.id_apply (X := Γ(⨁ f, W)) x]
  rw [← Hom.id_app, ← biproduct.total, Hom.sum_app_apply]
  rfl

lemma biproduct_π_app_sum_ι_app [DecidableEq J] (c : ∀ j, Γ(f j, W)) (j : J) :
    (biproduct.π f j).app W (∑ i, (biproduct.ι f i).app W (c i)) = c j := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, biproduct.ι_π_self, Hom.id_app]
    rfl
  · intro i _ hi
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, biproduct.ι_π_ne _ hi, Hom.zero_app]
    rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The sections of a finite biproduct are the families of sections of the summands. -/
lemma bijective_biproduct_π_app :
    Function.Bijective fun (x : Γ(⨁ f, W)) (j : J) ↦ (biproduct.π f j).app W x := by
  classical
  refine ⟨fun x x' h ↦ ?_, fun c ↦ ⟨∑ i, (biproduct.ι f i).app W (c i),
    funext fun j ↦ biproduct_π_app_sum_ι_app f W c j⟩⟩
  rw [biproduct_app_eq_sum f W x, biproduct_app_eq_sum f W x']
  exact Finset.sum_congr rfl fun j _ ↦ congrArg _ (congrFun h j)

end BiproductSections

/-- Restriction along an equality of opens is bijective. -/
lemma bijective_presheaf_map_of_eq (M : X.Modules) {W W' : X.Opens} (h : W' ≤ W) (h' : W ≤ W') :
    Function.Bijective (M.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  rw [Subsingleton.elim (homOfLE h) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  exact ConcreteCategory.bijective_of_isIso _

section CechSections

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → X.Opens) (W : X.Opens)

lemma le_image_preimage_iInf {k : ℕ} (y : Fin (k + 1) → ι) :
    ⨅ l, (W ⊓ V (y l)) ≤ (⨅ l, V (y l)).ι ''ᵁ ((⨅ l, V (y l)).ι ⁻¹ᵁ W) := by
  rw [image_preimage_ι]
  exact le_inf (le_iInf fun l ↦ (iInf_le _ l).trans inf_le_right)
    ((iInf_le _ 0).trans inf_le_left)

lemma image_preimage_iInf_le {k : ℕ} (y : Fin (k + 1) → ι) :
    (⨅ l, V (y l)).ι ''ᵁ ((⨅ l, V (y l)).ι ⁻¹ᵁ W) ≤ ⨅ l, (W ⊓ V (y l)) := by
  rw [image_preimage_ι]
  exact le_iInf fun l ↦ le_inf inf_le_right (inf_le_left.trans (iInf_le _ l))

/-- The sections over `W` of the sheafified Čech complex in degree `k` are the Čech cochains of
the family `W ⊓ V i`. -/
noncomputable def cechSheafXSections (k : ℕ) :
    Γ(cechSheafX ℱ V k, W) →+ TopCat.Presheaf.CechCochain (fun i ↦ W ⊓ V i) ℱ.presheaf k where
  toFun x y := ℱ.presheaf.map (homOfLE (le_image_preimage_iInf V W y)).op
    ((biproduct.π _ y).app W x)
  map_zero' := funext fun _ ↦ by simp only [map_zero]; rfl
  map_add' x x' := funext fun _ ↦ by simp only [map_add]; rfl

lemma cechSheafXSections_apply (k : ℕ) (x : Γ(cechSheafX ℱ V k, W)) (y : Fin (k + 1) → ι) :
    cechSheafXSections ℱ V W k x y = ℱ.presheaf.map (homOfLE (le_image_preimage_iInf V W y)).op
      ((biproduct.π _ y).app W x) := rfl

lemma bijective_cechSheafXSections (k : ℕ) :
    Function.Bijective (cechSheafXSections ℱ V W k) := by
  have h₁ := bijective_biproduct_π_app (fun y : Fin (k + 1) → ι ↦ ℱ.extendRestrict (⨅ l, V (y l)))
    W
  have h₂ : Function.Bijective fun (c : ∀ y : Fin (k + 1) → ι,
      Γ(ℱ.extendRestrict (⨅ l, V (y l)), W)) y ↦
        ℱ.presheaf.map (homOfLE (le_image_preimage_iInf V W y)).op (c y) :=
    Function.Bijective.piMap fun y ↦ bijective_presheaf_map_of_eq ℱ _
      (image_preimage_iInf_le V W y)
  exact h₂.comp h₁

/-- The sections over `W` of the sheafified Čech cosimplicial object are the Čech cosimplicial
abelian group of the family `W ⊓ V i`. -/
noncomputable def cechSheafSectionsCosimplicialIso :
    cechSheafCosimplicial ℱ V ⋙ sectionsFunctor W ≅
      (TopCat.Presheaf.cechCosimplicialObject (fun i ↦ W ⊓ V i)).obj ℱ.presheaf :=
  NatIso.ofComponents (fun k ↦ (AddEquiv.ofBijective (cechSheafXSections ℱ V W k.len)
    (bijective_cechSheafXSections ℱ V W k.len)).toAddCommGrpIso) fun {m n} θ ↦ by
      ext x
      funext z
      change cechSheafXSections ℱ V W n.len ((cechSheafMap ℱ V θ.toOrderHom).app W x) z =
        ℱ.presheaf.map _ (cechSheafXSections ℱ V W m.len x (z ∘ θ.toOrderHom))
      rw [cechSheafXSections_apply, cechSheafXSections_apply, ← ConcreteCategory.comp_apply
        (Hom.app _ W), ← Hom.comp_app, cechSheafMap_π, Hom.comp_app, ConcreteCategory.comp_apply,
        extendRestrictMap_app, presheaf_map_map_apply, presheaf_map_map_apply]
      rfl

/-- An additive functor commutes with the alternating coface map complex. -/
noncomputable def mapAlternatingCofaceMapComplexIso {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) :
    (F.mapHomologicalComplex _).obj ((AlgebraicTopology.alternatingCofaceMapComplex C).obj A) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex D).obj (A ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i _ rfl
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
      Iso.refl_hom, Category.id_comp, Category.comp_id]
    erw [CochainComplex.of_d, CochainComplex.of_d]
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum,
      Functor.map_zsmul]
    rfl)

/-- **The sections of the sheafified Čech complex.** The sections over `W` of `𝒞(V, ℱ)` form
the Čech complex of the family `W ⊓ V i` with values in `ℱ`. -/
noncomputable def cechSheafSectionsIso :
    ((sectionsFunctor W).mapHomologicalComplex _).obj (cechSheafComplex ℱ V) ≅
      (TopCat.Presheaf.cechComplex (fun i ↦ W ⊓ V i)).obj ℱ.presheaf :=
  mapAlternatingCofaceMapComplexIso (sectionsFunctor W) (cechSheafCosimplicial ℱ V) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cechSheafSectionsCosimplicialIso ℱ V W)

lemma cechSheafSectionsIso_hom_f_apply (k : ℕ) (x : Γ(cechSheafX ℱ V k, W)) :
    (cechSheafSectionsIso ℱ V W).hom.f k x = cechSheafXSections ℱ V W k x := rfl

end CechSections

section Resolution

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → X.Opens)

include V in
lemma exists_mem_of_iSup_eq_top (hV : ⨆ i, V i = ⊤) (x : X) : ∃ i, x ∈ V i :=
  Opens.mem_iSup.1 (by rw [hV]; trivial)

/-- The sheafified Čech complex of a cover is exact in positive degrees: on the opens contained
in some `V i`, its sections form the Čech complex of a family one of whose members contains all
the others. -/
theorem exactAt_cechSheafComplex (hV : ⨆ i, V i = ⊤) (q : ℕ) :
    (cechSheafComplex ℱ V).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)]
  refine ShortComplex.exact_of_exact_sectionsFunctor _ fun W x hx ↦ ?_
  obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top V hV x
  refine ⟨W ⊓ V i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  have h := TopCat.Presheaf.exactAt_cechComplex_of_le (fun j ↦ (W ⊓ V i) ⊓ V j) ℱ.presheaf
    (j := i) (fun j ↦ by simp) q
  have h' := h.of_iso (cechSheafSectionsIso ℱ V (W ⊓ V i)).symm
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)] at h'
  exact h'

/-- The augmentation `ℱ ⟶ 𝒞⁰(V, ℱ)` of a cover is injective on sections. -/
lemma injective_cechSheafAug_app (hV : ⨆ i, V i = ⊤) (W : X.Opens) :
    Function.Injective ((cechSheafAug ℱ V).app W) := by
  intro m m' h
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨ℱ.presheaf, ℱ.isSheaf⟩ (fun i ↦ W ⊓ V i) W
    (fun i ↦ homOfLE inf_le_left) (fun x hx ↦ ?_) m m' fun i ↦ ?_
  · obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top V hV x
    exact Opens.mem_iSup.2 ⟨i, hx, hi⟩
  · have := congrArg ((biproduct.π _ (fun _ : Fin 1 ↦ i)).app W) h
    simp only [← ConcreteCategory.comp_apply, ← Hom.comp_app, cechSheafAug_π] at this
    rw [extendRestrictUnit_app, extendRestrictUnit_app] at this
    have h₁ : W ⊓ V i ≤ (⨅ l : Fin 1, V ((fun _ ↦ i) l)).ι ''ᵁ
        ((⨅ l : Fin 1, V ((fun _ ↦ i) l)).ι ⁻¹ᵁ W) := by
      rw [image_preimage_ι]
      exact le_inf (le_iInf fun _ ↦ inf_le_right) inf_le_left
    have := congrArg (ℱ.presheaf.map (homOfLE h₁).op) this
    simp only [presheaf_map_map_apply] at this
    exact this

/-- `ℱ ⟶ 𝒞⁰(V, ℱ) ⟶ 𝒞¹(V, ℱ)` is exact for a cover: a Čech `0`-cocycle glues. -/
lemma exact_cechSheafAug (hV : ⨆ i, V i = ⊤) :
    (ShortComplex.mk (cechSheafAug ℱ V) ((cechSheafComplex ℱ V).d 0 1)
      (cechSheafAug_d ℱ V)).Exact := by
  refine ShortComplex.exact_of_exact_sectionsFunctor _ fun W x hx ↦ ?_
  obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top V hV x
  refine ⟨W ⊓ V i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  rw [ShortComplex.ab_exact_iff]
  intro c hc
  change Γ(cechSheafX ℱ V 0, W ⊓ V i) at c
  change ((cechSheafComplex ℱ V).d 0 1).app (W ⊓ V i) c = 0 at hc
  -- the component of `c` at the index `i`, a section over `W ⊓ V i`
  let y₀ : Fin 1 → ι := fun _ ↦ i
  have hy₀ : W ⊓ V i ≤ (⨅ l, V (y₀ l)).ι ''ᵁ ((⨅ l, V (y₀ l)).ι ⁻¹ᵁ (W ⊓ V i)) := by
    rw [image_preimage_ι]
    exact le_inf (le_iInf fun _ ↦ inf_le_right) le_rfl
  refine ⟨ℱ.presheaf.map (homOfLE hy₀).op ((biproduct.π _ y₀).app _ c),
    (bijective_biproduct_π_app _ _).1 (funext fun z ↦ ?_)⟩
  change (biproduct.π _ z).app _ ((cechSheafAug ℱ V).app _ _) = (biproduct.π _ z).app _ c
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, cechSheafAug_π, extendRestrictUnit_app,
    presheaf_map_map_apply]
  -- the cocycle condition at the index `(i, z 0)`
  let y : Fin 2 → ι := ![i, z 0]
  have hd := congrArg ((biproduct.π _ y).app (W ⊓ V i)) hc
  rw [cechSheafComplex_d, map_zero, Fin.sum_univ_two, Hom.add_app] at hd
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Hom.neg_app] at hd
  change (cechSheafMap ℱ V (Fin.succAbove 0) ≫ biproduct.π _ y).app _ c -
    (cechSheafMap ℱ V (Fin.succAbove 1) ≫ biproduct.π _ y).app _ c = 0 at hd
  rw [cechSheafMap_π, cechSheafMap_π, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, extendRestrictMap_app, extendRestrictMap_app,
    sub_eq_zero] at hd
  have hz : y ∘ Fin.succAbove 0 = z := funext fun l ↦ by
    fin_cases l
    rfl
  have hi' : y ∘ Fin.succAbove 1 = y₀ := funext fun l ↦ by
    fin_cases l
    rfl
  -- both sides are the restrictions of the two components of `c` to `W ⊓ V i ⊓ V (z 0)`
  have hle : (⨅ l, V (z l)).ι ''ᵁ ((⨅ l, V (z l)).ι ⁻¹ᵁ (W ⊓ V i)) ≤
      (⨅ l, V (y l)).ι ''ᵁ ((⨅ l, V (y l)).ι ⁻¹ᵁ (W ⊓ V i)) := by
    rw [image_preimage_ι, image_preimage_ι]
    refine le_inf (le_iInf fun l ↦ ?_) inf_le_right
    fin_cases l
    · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_left.trans (iInf_le _ 0)
  have hd' := congrArg (ℱ.presheaf.map (homOfLE hle).op) hd
  clear_value y
  subst hz
  rw [presheaf_map_map_apply, presheaf_map_map_apply] at hd'
  refine (Eq.trans ?_ hd'.symm).trans ?_
  · conv_rhs => rw [← hi']
    rfl
  · refine (presheaf_map_id_apply _ _ _)

/-- **The sheafified Čech complex of a cover is a resolution.** -/
instance quasiIso_cechSheafι [Fact (⨆ i, V i = ⊤)] : QuasiIso (cechSheafι ℱ V) := by
  have hV : ⨆ i, V i = ⊤ := Fact.out
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨exact_cechSheafAug ℱ V hV, mono_of_injective_app _ (injective_cechSheafAug_app ℱ V hV)⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [cechSheafι])
        (by simp)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact exactAt_cechSheafComplex ℱ V hV n
    · exact CochainComplex.exactAt_succ_single_obj _ _

end Resolution

end AlgebraicGeometry.Scheme.Modules
