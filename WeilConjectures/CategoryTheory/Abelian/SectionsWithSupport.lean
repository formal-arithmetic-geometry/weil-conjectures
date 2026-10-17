/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Sections with support in a closed part

We work in an abstract *open–closed situation*: abelian categories `𝒳`, `𝒵`, `𝒱` (sheaves on
`X`, on a closed part `Z` and on its open complement `V`), with adjunctions `i^* ⊣ i_*` and
`j^* ⊣ j_*` such that

* `i^*`, `j^*` are exact and `i_*` is exact,
* the counits `i^* i_* ⟶ 𝟭` and `j^* j_* ⟶ 𝟭` are invertible (`i_*`, `j_*` fully faithful),
* `j^* i_* = 0`, and `i^*`, `j^*` jointly detect zero objects.

The functor of *sections with support in `Z`* is `Γ_Z(M) = i^* ker(M ⟶ j_* j^* M)`
(`CategoryTheory.SectionsWithSupport.functor`). We show (blueprint
`det-lem-formal-closed-support-adjunction`, whose proof only uses these properties):

1. `ker(M ⟶ j_* j^* M) ≅ i_* Γ_Z(M)` and `Γ_Z` is right adjoint to `i_*`
   (`CategoryTheory.SectionsWithSupport.adjunction`); in particular it is left exact;
2. `RΓ_Z` is right adjoint to `i_*` on the derived categories
   (`CategoryTheory.SectionsWithSupport.derivedAdjunction`);
3. given moreover an exact left adjoint `j_! ⊣ j^*` with invertible unit and `i^* j_! = 0`, the
   unit `I ⟶ j_* j^* I` is an epimorphism for every injective `I`
   (`CategoryTheory.SectionsWithSupport.epi_unit_app_of_injective`);
4. the counit `i_* RΓ_Z K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a distinguished
   triangle, with a unique third map, natural in `K`
   (`CategoryTheory.SectionsWithSupport.existsUnique_distTriang`), and
   `RΓ_Z K ≅ i^* fib(K ⟶ Rj_* j^* K)`
   (`CategoryTheory.SectionsWithSupport.nonempty_iso_upperStar_fib`).
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Abelian

namespace CategoryTheory.SectionsWithSupport

variable {𝒳 𝒵 𝒱 : Type*} [Category 𝒳] [Category 𝒵] [Category 𝒱] [Abelian 𝒳] [Abelian 𝒵]
  [Abelian 𝒱] {iUp : 𝒳 ⥤ 𝒵} {iLow : 𝒵 ⥤ 𝒳} {jUp : 𝒳 ⥤ 𝒱} {jLow : 𝒱 ⥤ 𝒳}
  (adjI : iUp ⊣ iLow) (adjJ : jUp ⊣ jLow)
  [iUp.Additive] [iLow.Additive] [jUp.Additive] [jLow.Additive]
  [PreservesFiniteLimits iUp] [PreservesFiniteColimits iUp]
  [PreservesFiniteLimits jUp] [PreservesFiniteColimits jUp]
  [IsIso adjI.counit] [IsIso adjJ.counit]

section Sheaves

/-- If the counit of `j^* ⊣ j_*` is invertible, `j^*` inverts the unit `M ⟶ j_* j^* M`. -/
lemma isIso_map_unit_app (M : 𝒳) : IsIso (jUp.map (adjJ.unit.app M)) := by
  have : IsIso (jUp.map (adjJ.unit.app M) ≫ adjJ.counit.app (jUp.obj M)) := by
    rw [adjJ.left_triangle_components M]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adjJ.counit.app _)

variable {adjJ} in
include adjI in
/-- A morphism of `𝒳` inverted by `i^*` and `j^*` is an isomorphism, when `i^*` and `j^*` are
exact and jointly detect zero objects. -/
lemma isIso_of_isIso_map (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F)
    {M N : 𝒳} (u : M ⟶ N) [IsIso (iUp.map u)] [IsIso (jUp.map u)] : IsIso u := by
  have hk : IsZero (kernel u) := hdet _
    ((isZero_kernel_of_mono (iUp.map u)).of_iso (PreservesKernel.iso iUp u))
    ((isZero_kernel_of_mono (jUp.map u)).of_iso (PreservesKernel.iso jUp u))
  have hc : IsZero (cokernel u) := hdet _
    ((isZero_cokernel_of_epi (iUp.map u)).of_iso (PreservesCokernel.iso iUp u))
    ((isZero_cokernel_of_epi (jUp.map u)).of_iso (PreservesCokernel.iso jUp u))
  have := Preadditive.mono_of_isZero_kernel u hk
  have := Preadditive.epi_of_isZero_cokernel u hc
  exact isIso_of_mono_of_epi u

include adjJ in
/-- An object `N` with `j^* N = 0` is `i_*` of `i^* N`: the unit `N ⟶ i_* i^* N` is an
isomorphism. -/
lemma isIso_unit_app_of_isZero (h₀ : ∀ A, IsZero (jUp.obj (iLow.obj A)))
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F) {N : 𝒳}
    (hN : IsZero (jUp.obj N)) : IsIso (adjI.unit.app N) := by
  have : IsIso (iUp.map (adjI.unit.app N)) := by
    have : IsIso (iUp.map (adjI.unit.app N) ≫ adjI.counit.app (iUp.obj N)) := by
      rw [adjI.left_triangle_components N]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adjI.counit.app _)
  have : IsIso (jUp.map (adjI.unit.app N)) :=
    isIso_of_source_target_iso_zero _ hN.isoZero (h₀ _).isoZero
  exact isIso_of_isIso_map adjI hdet _

/-- `j^*` kills the kernel of the unit `M ⟶ j_* j^* M`. -/
lemma isZero_upperStar_kernel (M : 𝒳) : IsZero (jUp.obj (kernel (adjJ.unit.app M))) :=
  have := isIso_map_unit_app adjJ M
  (isZero_kernel_of_mono (jUp.map (adjJ.unit.app M))).of_iso (PreservesKernel.iso jUp _)

include adjI in
/-- A morphism `i_* A ⟶ M` composes to zero with the unit `M ⟶ j_* j^* M`. -/
lemma comp_unit_app_eq_zero (h₀ : ∀ A, IsZero (jUp.obj (iLow.obj A))) {A : 𝒵} {M : 𝒳}
    (f : iLow.obj A ⟶ M) : f ≫ adjJ.unit.app M = 0 := by
  rw [← adjJ.unit_naturality f, ((jLow.map_isZero (h₀ A)).eq_of_tgt
    (adjJ.unit.app (iLow.obj A)) 0), zero_comp]

variable (h₀ : ∀ A, IsZero (jUp.obj (iLow.obj A)))
  (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (jUp.obj F) → IsZero F)

/-- The bijection `Hom(i_* A, M) ≃ Hom(A, i^* ker(M ⟶ j_* j^* M))`. -/
noncomputable def homEquiv (A : 𝒵) (M : 𝒳) :
    (iLow.obj A ⟶ M) ≃ (A ⟶ iUp.obj (kernel (adjJ.unit.app M))) :=
  have := isIso_unit_app_of_isZero adjI adjJ h₀ hdet (isZero_upperStar_kernel adjJ M)
  { toFun f := adjI.fullyFaithfulROfIsIsoCounit.preimage
      (kernel.lift _ f (comp_unit_app_eq_zero adjI adjJ h₀ f) ≫
        adjI.unit.app (kernel (adjJ.unit.app M)))
    invFun g := iLow.map g ≫ inv (adjI.unit.app (kernel (adjJ.unit.app M))) ≫ kernel.ι _
    left_inv f := by simp
    right_inv g := by
      apply adjI.fullyFaithfulROfIsIsoCounit.map_injective
      simp only [Functor.FullyFaithful.map_preimage]
      have : kernel.lift (adjJ.unit.app M) (iLow.map g ≫
          inv (adjI.unit.app (kernel (adjJ.unit.app M))) ≫ kernel.ι _)
          (by simp [comp_unit_app_eq_zero adjI adjJ h₀]) =
          iLow.map g ≫ inv (adjI.unit.app (kernel (adjJ.unit.app M))) := by
        ext; simp
      simp [this] }

/-- **Sections with support in the closed part** (blueprint
`det-lem-formal-closed-support-adjunction`): the functor `Γ_Z(M) = i^* ker(M ⟶ j_* j^* M)`,
right adjoint to `i_*`. -/
noncomputable def functor : 𝒳 ⥤ 𝒵 :=
  Adjunction.rightAdjointOfEquiv (G_obj := fun M ↦ iUp.obj (kernel (adjJ.unit.app M)))
    (homEquiv adjI adjJ h₀ hdet) (fun A A' M f g ↦ by
      apply adjI.fullyFaithfulROfIsIsoCounit.map_injective
      simp only [homEquiv, Equiv.coe_fn_mk, Functor.FullyFaithful.map_preimage, Functor.map_comp]
      have : kernel.lift (adjJ.unit.app M) (iLow.map f ≫ g)
          (comp_unit_app_eq_zero adjI adjJ h₀ _) =
          iLow.map f ≫ kernel.lift _ g (comp_unit_app_eq_zero adjI adjJ h₀ g) := by
        ext; simp
      simp [this])

/-- The value of `Γ_Z` on `M` is `i^* ker(M ⟶ j_* j^* M)`. -/
lemma functor_obj (M : 𝒳) :
    (functor adjI adjJ h₀ hdet).obj M = iUp.obj (kernel (adjJ.unit.app M)) :=
  rfl

/-- **`i_* ⊣ Γ_Z`** (blueprint `det-lem-formal-closed-support-adjunction` (1)). -/
noncomputable def adjunction : iLow ⊣ functor adjI adjJ h₀ hdet :=
  Adjunction.adjunctionOfEquivRight _ _

/-- `Γ_Z` is left exact, being a right adjoint. -/
lemma preservesFiniteLimits_functor : PreservesFiniteLimits (functor adjI adjJ h₀ hdet) :=
  have := (adjunction adjI adjJ h₀ hdet).isRightAdjoint
  inferInstance

/-- **`ker(M ⟶ j_* j^* M) ≅ i_* Γ_Z(M)`** (blueprint `det-lem-formal-closed-support-adjunction`
(1)). -/
noncomputable def kernelIso (M : 𝒳) :
    kernel (adjJ.unit.app M) ≅ iLow.obj ((functor adjI adjJ h₀ hdet).obj M) :=
  have := isIso_unit_app_of_isZero adjI adjJ h₀ hdet (isZero_upperStar_kernel adjJ M)
  asIso (adjI.unit.app (kernel (adjJ.unit.app M)))

/-- `Γ_Z` is additive, being right adjoint to an additive functor. -/
instance additive_functor : (functor adjI adjJ h₀ hdet).Additive :=
  (adjunction adjI adjJ h₀ hdet).right_adjoint_additive

section Injective

variable {jShriek : 𝒱 ⥤ 𝒳} (adjS : jShriek ⊣ jUp) [IsIso adjS.unit]

include adjI h₀ hdet in
/-- The comparison `j_! V ⟶ j_* V`, adjoint to the inverse of the counit `j^* j_* V ≅ V`, is a
monomorphism when `j_!` is exact, `i^* j_! = 0`, and `i^*`, `j^*` jointly detect zero objects. -/
lemma mono_comparison [PreservesFiniteLimits jShriek] [jShriek.Additive]
    (h₁ : ∀ V, IsZero (iUp.obj (jShriek.obj V))) (V : 𝒱) :
    Mono ((adjS.homEquiv _ _).symm (inv (adjJ.counit.app V))) := by
  set m := (adjS.homEquiv _ _).symm (inv (adjJ.counit.app V))
  have hm : adjS.unit.app V ≫ jUp.map m = inv (adjJ.counit.app V) :=
    (adjS.homEquiv_unit _ _ m).symm.trans ((adjS.homEquiv _ _).apply_symm_apply _)
  have : IsIso (jUp.map m) := by
    have : IsIso (adjS.unit.app V ≫ jUp.map m) := by rw [hm]; infer_instance
    exact IsIso.of_isIso_comp_left (adjS.unit.app V) _
  refine Preadditive.mono_of_isZero_kernel m (hdet _ ?_
    ((isZero_kernel_of_mono (jUp.map m)).of_iso (PreservesKernel.iso jUp m)))
  have hz : IsZero (iUp.obj (jShriek.obj V)) := h₁ V
  exact IsZero.of_mono (iUp.map (kernel.ι m)) hz

include adjI h₀ hdet adjS in
/-- Blueprint `det-lem-formal-closed-support-adjunction` (3): for an injective object `I`, the
unit `I ⟶ j_* j^* I` is an epimorphism (indeed a split epimorphism). The counit
`j_! j^* I ⟶ I` extends along the monomorphism `j_! j^* I ⟶ j_* j^* I` to `s : j_* j^* I ⟶ I`,
and `s` followed by the unit is the identity, `j_*` being fully faithful. -/
lemma epi_unit_app_of_injective [PreservesFiniteLimits jShriek] [jShriek.Additive]
    (h₁ : ∀ V, IsZero (iUp.obj (jShriek.obj V))) (I : 𝒳) [Injective I] :
    Epi (adjJ.unit.app I) := by
  set V := jUp.obj I
  set m := (adjS.homEquiv _ _).symm (inv (adjJ.counit.app V))
  have := mono_comparison adjI adjJ h₀ hdet adjS h₁ V
  let c : jShriek.obj V ⟶ I := adjS.counit.app I
  let s : jLow.obj V ⟶ I := Injective.factorThru c m
  have hs : m ≫ s = adjS.counit.app I := Injective.comp_factorThru c m
  have hm : adjS.unit.app V ≫ jUp.map m = inv (adjJ.counit.app V) :=
    (adjS.homEquiv_unit _ _ m).symm.trans ((adjS.homEquiv _ _).apply_symm_apply _)
  have hc : adjS.unit.app V ≫ jUp.map (adjS.counit.app I) = 𝟙 _ :=
    adjS.right_triangle_components I
  -- `j^* s` is the counit of `j^* ⊣ j_*`
  have hjs : jUp.map s = adjJ.counit.app V := by
    have h := congrArg (fun φ ↦ adjS.unit.app V ≫ φ) (congrArg jUp.map hs)
    rw [Functor.map_comp, ← Category.assoc, hm, hc] at h
    rw [← cancel_epi (inv (adjJ.counit.app V)), h, IsIso.inv_hom_id]
  -- `s ≫ unit = 𝟙`, by full faithfulness of `j_*`
  have hsplit : s ≫ adjJ.unit.app I = 𝟙 _ := by
    apply (adjJ.homEquiv _ _).symm.injective
    simp [Adjunction.homEquiv_counit, hjs]
    rfl
  exact epi_of_epi_fac hsplit

end Injective

section Derived

variable [HasDerivedCategory 𝒳] [HasDerivedCategory 𝒵] [HasDerivedCategory 𝒱]
  [HasKInjectiveResolutions 𝒳] [HasKInjectiveResolutions 𝒵] [HasKInjectiveResolutions 𝒱]
  [PreservesFiniteColimits iLow] [PreservesFiniteLimits iLow]

/-- **`D(i_*) ⊣ RΓ_Z`** (blueprint `det-lem-formal-closed-support-adjunction` (2)): the derived
functor of sections with support in `Z` is right adjoint to `i_*` on the derived categories,
`Hom_{D(X)}(i_* A, K) ≅ Hom_{D(Z)}(A, RΓ_Z K)`, as `i_*` is exact. -/
noncomputable def derivedAdjunction :
    iLow.mapDerivedCategory ⊣ (functor adjI adjJ h₀ hdet).rightDerivedFunctor :=
  (adjunction adjI adjJ h₀ hdet).mapDerivedCategoryRightDerivedAdjunction

/-- The adjunction `D(i^*) ⊣ D(i_*)`. -/
noncomputable def derivedUpperLowerAdjunctionI :
    iUp.mapDerivedCategory ⊣ iLow.mapDerivedCategory :=
  adjI.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    iLow.rightDerivedFunctorIsoMapDerivedCategory

include adjI in
/-- `D(i_*)` is fully faithful: `D(i^*) D(i_*) ≅ D(i^* i_*) ≅ 𝟭`. -/
noncomputable def fullyFaithfulMapDerivedCategoryILow : iLow.mapDerivedCategory.FullyFaithful :=
  have : PreservesFiniteLimits (iLow ⋙ iUp) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (iLow ⋙ iUp) := comp_preservesFiniteColimits _ _
  (derivedUpperLowerAdjunctionI adjI).fullyFaithfulROfCompIsoId
    ((iLow.mapDerivedCategoryCompIso iUp).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adjI.counit) ≪≫ Functor.mapDerivedCategoryIdIso _)

/-- The adjunction `D(j^*) ⊣ Rj_*`. -/
noncomputable abbrev derivedAdjunctionJ : jUp.mapDerivedCategory ⊣ jLow.rightDerivedFunctor :=
  adjJ.mapDerivedCategoryRightDerivedAdjunction

instance isIso_derivedAdjunctionJ_counit : IsIso (derivedAdjunctionJ adjJ).counit :=
  have := adjJ.preservesKInjectiveComplexes
  have h := adjJ.fullyFaithfulROfIsIsoCounit
  have := h.full
  have := h.faithful
  adjJ.mapDerivedCategoryRightDerivedAdjunction.counit_isIso_of_R_fully_faithful

include h₀ in
lemma isZero_mapDerivedCategory_jUp_iLow (M : DerivedCategory 𝒵) :
    IsZero (jUp.mapDerivedCategory.obj (iLow.mapDerivedCategory.obj M)) :=
  have : PreservesFiniteLimits (iLow ⋙ jUp) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (iLow ⋙ jUp) := comp_preservesFiniteColimits _ _
  (Functor.isZero_mapDerivedCategory_obj (iLow ⋙ jUp) M fun _ ↦ h₀ _).of_iso
    ((iLow.mapDerivedCategoryCompIso jUp).symm.app M)

include adjI hdet in
lemma isZero_of_isZero_mapDerivedCategory {K : DerivedCategory 𝒳}
    (hi : IsZero (iUp.mapDerivedCategory.obj K)) (hj : IsZero (jUp.mapDerivedCategory.obj K)) :
    IsZero K :=
  (DerivedCategory.isZero_iff _).2 fun n ↦ hdet _
    (((DerivedCategory.isZero_iff _).1 hi n).of_iso
      ((iUp.mapDerivedCategoryHomologyFunctorIso n).app K))
    (((DerivedCategory.isZero_iff _).1 hj n).of_iso
      ((jUp.mapDerivedCategoryHomologyFunctorIso n).app K))

include adjI h₀ hdet in
/-- A complex `K` with `j^* K = 0` lies in the essential image of `D(i_*)`. -/
lemma mapDerivedCategory_essImage_of_isZero {K : DerivedCategory 𝒳}
    (hK : IsZero (jUp.mapDerivedCategory.obj K)) : iLow.mapDerivedCategory.essImage K := by
  set adj := derivedUpperLowerAdjunctionI adjI
  have hFF := fullyFaithfulMapDerivedCategoryILow adjI
  have := hFF.full
  have := hFF.faithful
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  obtain ⟨W, v, w, h₁⟩ := distinguished_cocone_triangle (adj.unit.app K)
  have hiu : IsIso (iUp.mapDerivedCategory.map (adj.unit.app K)) :=
    have := IsIso.id (iUp.mapDerivedCategory.obj K)
    IsIso.of_isIso_fac_right (adj.left_triangle_components K)
  have hju : IsIso (jUp.mapDerivedCategory.map (adj.unit.app K)) :=
    isIso_of_source_target_iso_zero _ hK.isoZero
      (isZero_mapDerivedCategory_jUp_iLow h₀ _).isoZero
  have hW : IsZero W := isZero_of_isZero_mapDerivedCategory adjI hdet
    ((Triangle.isZero₃_iff_isIso₁ _ (iUp.mapDerivedCategory.map_distinguished _ h₁)).2 hiu)
    ((Triangle.isZero₃_iff_isIso₁ _ (jUp.mapDerivedCategory.map_distinguished _ h₁)).2 hju)
  exact ⟨_, ⟨(@asIso _ _ _ _ (adj.unit.app K) ((Triangle.isZero₃_iff_isIso₁ _ h₁).1 hW)).symm⟩⟩

/-- Blueprint `det-lem-formal-closed-support-adjunction` (4): for `K` in `D(X)`, the counit
`i_* RΓ_Z K ⟶ K` of `D(i_*) ⊣ RΓ_Z` and the unit `K ⟶ Rj_* j^* K` of `D(j^*) ⊣ Rj_*` extend to a
distinguished triangle `i_* RΓ_Z K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* RΓ_Z K)[1]`, with a unique third
map. It is natural in `K` (`CategoryTheory.Pretriangulated.Recollement.exists_triangleHom`). -/
theorem existsUnique_distTriang (K : DerivedCategory 𝒳) :
    ∃! w, Recollement.triangle (derivedAdjunctionJ adjJ) (derivedAdjunction adjI adjJ h₀ hdet) K w ∈
      distTriang _ :=
  Recollement.existsUnique_distTriang_counit_unit _ _ (fullyFaithfulMapDerivedCategoryILow adjI)
    (isZero_mapDerivedCategory_jUp_iLow h₀)
    (fun _ hK ↦ mapDerivedCategory_essImage_of_isZero adjI h₀ hdet hK) K

/-- Blueprint `det-lem-formal-closed-support-adjunction` (4): `RΓ_Z K ≅ i^* fib(K ⟶ Rj_* j^* K)`:
for every distinguished triangle `F ⟶ K ⟶ Rj_* j^* K ⟶ F[1]` whose second map is the unit,
`D(i^*) F ≅ RΓ_Z K`. -/
theorem nonempty_iso_upperStar_fib (K : DerivedCategory 𝒳) {F : DerivedCategory 𝒳}
    (a : F ⟶ K) (δ : jLow.rightDerivedFunctor.obj (jUp.mapDerivedCategory.obj K) ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((derivedAdjunctionJ adjJ).unit.app K) δ ∈ distTriang _) :
    Nonempty (iUp.mapDerivedCategory.obj F ≅
      (functor adjI adjJ h₀ hdet).rightDerivedFunctor.obj K) := by
  obtain ⟨w, hw, -⟩ := existsUnique_distTriang adjI adjJ h₀ hdet K
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ (rot_of_distTriang _ hT)
    (rot_of_distTriang _ hw) (Iso.refl _)
  have hFF := fullyFaithfulMapDerivedCategoryILow adjI
  have := hFF.full
  have := hFF.faithful
  let e₁ : F ≅ iLow.mapDerivedCategory.obj ((functor adjI adjJ h₀ hdet).rightDerivedFunctor.obj K) :=
    (shiftFunctor _ (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)
  have : IsIso (derivedUpperLowerAdjunctionI adjI).counit :=
    (derivedUpperLowerAdjunctionI adjI).counit_isIso_of_R_fully_faithful
  exact ⟨iUp.mapDerivedCategory.mapIso e₁ ≪≫
    asIso ((derivedUpperLowerAdjunctionI adjI).counit.app _)⟩

end Derived

end Sheaves

end CategoryTheory.SectionsWithSupport
