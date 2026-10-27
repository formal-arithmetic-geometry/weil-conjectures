/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.RingTheory.Ideal.Maps
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.CategoryTheory.CommAlgebraSheafImage
import Sheaf.Topology.RingedSpaceGeneratedIdealTensor
import Sheaf.CategoryTheory.AlgebraSheafQuotientCokernel

/-! # Kernels, images, generated ideals and quotients of quasi-coherent algebras

Source: Stacks Project, Schemes, Tags 01IC and 01LA; Properties, Tags 05JS, 086N and 0817
(blueprint: lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal).

Ideal subsheaves are represented by module sheaves with sectionwise injective inclusions
and ideals equal to their section ranges. The image algebra is identified by its inclusion
and the local-preimage condition. The quotient presheaf is identified by sectionwise
surjective ring maps with the specified ideals as kernels; its sheafification and the
quotient algebra map are explicitly tied together by the sheafification unit.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.CommAlgebraSheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Comparing sheaf and module interfaces requires extra elaboration heartbeats.
/-- Kernels and images of morphisms of quasi-coherent algebra sheaves are quasi-coherent.
The kernel is computed on all opens; the locally defined image is computed sectionwise
on affine opens. Source: Stacks, Schemes, Tags 01IC and 01LA(5); Properties, Tag 0817
(blueprint: lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal).

Proof:
0. Every open is covered by affine opens (def-pc-scheme), and membership in a subsheaf
   can be checked on this cover.
1. The algebra map is linear. Its module kernel is computed sectionwise
   (def-weil-sheaf-of-modules-category), and is quasi-coherent by
   lem-weil-pbc-quasi-coherent-module-kernel. Ring-homomorphism kernels are ideals.
2. The module image, defined by local preimages, is quasi-coherent and its affine sections
   are the sectionwise image (lem-weil-pbc-quasi-coherent-module-cokernel-image).
   Locally lift two sections to prove closure under subtraction and multiplication;
   the unit and structure-ring sections are already images. Thus this module image
   is a subalgebra sheaf with the stated local and affine section ranges. -/
theorem kernel_image_quasiCoherent {X : Scheme.{u}} (B A : X.CommAlgebraSheaf)
    (hB : B.toModule.IsQuasicoherent) (hA : A.toModule.IsQuasicoherent) (ψ : B ⟶ A) :
    (∃ (J : X.Modules) (i : J ⟶ B.toModule), J.IsQuasicoherent ∧
      ∀ U : X.Opens, Function.Injective (i.app U) ∧
        Set.range (i.app U) =
          (RingHom.ker (ψ.right.hom.app (op U)).hom : Set (B.right.obj.obj (op U)))) ∧
    (∃ (D : X.CommAlgebraSheaf) (k : D ⟶ A), D.toModule.IsQuasicoherent ∧
      (∀ U : X.Opens, Function.Injective (k.right.hom.app (op U))) ∧
      (∀ (U : X.Opens) (s : A.right.obj.obj (op U)),
        s ∈ Set.range (k.right.hom.app (op U)) ↔
          ∀ x : X, x ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
            A.right.obj.map (homOfLE hVU).op s ∈ Set.range (ψ.right.hom.app (op V))) ∧
      (∀ (U : X.Opens), IsAffineOpen U →
        Set.range (k.right.hom.app (op U)) = Set.range (ψ.right.hom.app (op U)))) :=
  open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules in by
    classical
    let φ : B.toModule ⟶ A.toModule := (commAlgebraSheafModuleFunctor X.sheaf).map ψ
    have : B.toModule.IsQuasicoherent := hB
    have : A.toModule.IsQuasicoherent := hA
    have hφ := quasiCoherent_cokernel_image φ
    constructor
    · refine ⟨kernel φ, kernel.ι φ, isQuasicoherent_kernel φ, fun U ↦ ?_⟩
      exact ⟨injective_map_kernelι U φ, range_map_kernelι U φ⟩
    · obtain ⟨D, p, k, hpk, hk, hloc, hp, ⟨α, hα, hαp⟩, huni⟩ :=
        commAlgebraSheaf_image_factorization X.sheaf ψ
      let β : (commAlgebraSheafModuleFunctor X.sheaf).obj D ≅ Abelian.image φ :=
        α ≪≫ (Abelian.imageIsoImage φ).symm
      have hβ : β.hom ≫ Abelian.image.ι φ =
          (commAlgebraSheafModuleFunctor X.sheaf).map k := by
        have he : (Abelian.imageIsoImage φ).inv ≫ Abelian.image.ι φ = image.ι φ :=
          (Iso.inv_comp_eq _).mpr (Abelian.imageIsoImage_hom_comp_image_ι φ).symm
        exact (Category.assoc _ _ _).trans ((congrArg (α.hom ≫ ·) he).trans hα)
      have hr (U : X.Opens) :
          Set.range (k.right.hom.app (op U)) =
            Set.range ((Abelian.image.ι φ).val.app (op U)) := by
        have he := congrArg (fun f ↦ (f.val.app (op U) : _ → _)) hβ
        change (Abelian.image.ι φ).val.app (op U) ∘ β.hom.val.app (op U) =
          (k.right.hom.app (op U) : _ → _) at he
        rw [← he]
        exact (appLinearEquivOfIso β U).surjective.range_comp _
      refine ⟨D, k, (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        β.symm hφ.2.2.2.2.2.2.2.1, hk, ?_, ?_⟩
      · intro U s
        rw [hr]
        exact (hφ.2.2.1 U s).trans (by
          simp only [Set.mem_range]
          constructor <;> intro h x hx
          · obtain ⟨V, hV, hxV, t, ht⟩ := h x hx
            exact ⟨V, hV, hxV, t, ht⟩
          · obtain ⟨V, hV, hxV, t, ht⟩ := h x hx
            exact ⟨V, hV, hxV, t, ht⟩)
      · intro U hU
        rw [hr]
        exact (hφ.2.2.2.2.2.2.2.2 ⟨U, hU⟩).1


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Comparing sheaf and module interfaces requires extra elaboration heartbeats.
/-- The ideal generated by a quasi-coherent module in a quasi-coherent algebra, and the
quotient algebra, are quasi-coherent and computed on affine opens. The ideal is the
smallest ideal subsheaf containing the given module image, and is also the local image
of the sheafified tensor multiplication map. The quotient is the sheafification of the
sectionwise quotient rings, and has the algebra quotient universal property.
Source: Stacks, Schemes, Tags 01IC and 01LA(5),(8); Properties, Tags 05JS and 0817
(blueprint: lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal).

Proof:
0. Check subsheaf membership on an affine cover of each open (def-pc-scheme).
3. The sectionwise bilinear map (b,s) ↦ b e(s) induces the presheaf tensor map, then the
   unique sheafified tensor map (def-pur-sheaf-tensor-product, def-weil-pbc-sheafification).
   Its source is quasi-coherent and on affines is the tensor of the sections
   (lem-weil-pbc-quasi-coherent-tensor-product-affine-sections). Its local image is
   quasi-coherent, and on affines is the ideal spanned by e(E(U))
   (lem-weil-pbc-quasi-coherent-module-cokernel-image).
4. On affine opens that image is an ideal containing e(E). The affine cover criterion
   proves ideal closure and containment on all opens. Any ideal subsheaf containing
   e(E) contains it on affines, hence on all opens: it is the smallest such ideal.
5. Sheafify the sectionwise quotient ring presheaf. Ring sheafification is also abelian
   sheafification (lem-weil-pbc-ring-sheafification-space-underlying-abelian).
   Compare its underlying module with the module cokernel of the ideal inclusion:
   both universal properties give inverse maps. The module cokernel is quasi-coherent,
   its quotient map is locally surjective, and its affine section maps are surjective
   with the stated kernels (lem-weil-pbc-quasi-coherent-module-cokernel-image).
6. An algebra map killing e(E) has an ideal kernel containing the generated ideal by
   minimality. Factor each section map through the sectionwise quotient, then use ring
   sheafification to get the unique map from the quotient sheaf. It commutes with the
   structure morphism since the original map does. Sectionwise quotient surjectivity
   and sheafification uniqueness prove uniqueness of the algebra factorization. -/
theorem generated_ideal_quotient_quasiCoherent {X : Scheme.{u}}
    (B : X.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    (E : X.Modules) (hE : E.IsQuasicoherent) (e : E ⟶ B.toModule) :
    ∃ (J : X.Modules) (i : J ⟶ B.toModule)
      (I : ∀ U : X.Opens, Ideal (B.right.obj.obj (op U))),
      J.IsQuasicoherent ∧
      (∀ U : X.Opens, Function.Injective (i.app U) ∧
        Set.range (i.app U) = (I U : Set (B.right.obj.obj (op U)))) ∧
      (∀ U : X.Opens, Set.range (e.app U) ⊆ (I U : Set (B.right.obj.obj (op U)))) ∧
      (∀ (K : X.Modules) (j : K ⟶ B.toModule)
        (L : ∀ U : X.Opens, Ideal (B.right.obj.obj (op U))),
        (∀ U : X.Opens, Function.Injective (j.app U) ∧
          Set.range (j.app U) = (L U : Set (B.right.obj.obj (op U)))) →
        (∀ U : X.Opens, Set.range (e.app U) ⊆ (L U : Set (B.right.obj.obj (op U)))) →
        ∀ U : X.Opens, I U ≤ L U) ∧
      (∀ (U : X.Opens), IsAffineOpen U →
        I U = Ideal.span (Set.range (e.app U) : Set (B.right.obj.obj (op U)))) ∧
      (∃ μ : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
          (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) B.toModule.val E.val) ⟶
            B.toModule,
        (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (s : E.val.obj (op U)),
          μ.val.app (op U)
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
                B.toModule.val E.val)).app (op U) (b ⊗ₜ[X.presheaf.obj (op U)] s)) =
            @Mul.mul (B.right.obj.obj (op U)) inferInstance b (e.app U s)) ∧
        (∀ (U : X.Opens) (s : B.right.obj.obj (op U)), s ∈ I U ↔
          ∀ x : X, x ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
            B.right.obj.map (homOfLE hVU).op s ∈ Set.range (μ.val.app (op V)))) ∧
      (∃ (Q : X.CommAlgebraSheaf) (q : B ⟶ Q)
        (P : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}) (p : B.right.obj ⟶ P)
        (a : (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj P ≅ Q.right),
        (∀ U : X.Opens, Function.Surjective (p.app (op U)) ∧
          RingHom.ker (p.app (op U)).hom = I U) ∧
        q.right.hom = p ≫
          (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat).unit.app P ≫
            a.hom.hom ∧
        Q.toModule.IsQuasicoherent ∧
        (∀ (U : X.Opens) (s : Q.right.obj.obj (op U)),
          ∀ x : X, x ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
            Q.right.obj.map (homOfLE hVU).op s ∈ Set.range (q.right.hom.app (op V))) ∧
        (∀ (U : X.Opens), IsAffineOpen U →
          Function.Surjective (q.right.hom.app (op U)) ∧
            RingHom.ker (q.right.hom.app (op U)).hom = I U) ∧
        (∀ (C : X.CommAlgebraSheaf) (χ : B ⟶ C),
          (∀ (U : X.Opens) (s : E.val.obj (op U)),
            χ.right.hom.app (op U) (e.app U s) = 0) →
          ∃! χbar : Q ⟶ C, q ≫ χbar = χ)) :=
  open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules in by
    classical
    have : B.toModule.IsQuasicoherent := hB
    have : E.IsQuasicoherent := hE
    obtain ⟨μ, hμ, hμuniq, hideal, hchar, hcontains, hminimal⟩ :=
      RingedSpace.exists_generatedIdeal_tensor X.toRingedSpace B E e
    clear hμuniq hchar
    let P := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) B.toModule.val E.val
    let P' := SheafOfModules.siteTensorPresheaf B.toModule.val E.val
    let c : P ≅ P' :=
      { hom :=
          { app := fun U ↦ 𝟙 _
            naturality := by
              intro U V f
              apply ModuleCat.hom_ext
              apply TensorProduct.ext'
              intro b s
              rfl }
        inv :=
          { app := fun U ↦ 𝟙 _
            naturality := by
              intro U V f
              apply ModuleCat.hom_ext
              apply TensorProduct.ext'
              intro b s
              rfl } }
    let a := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso c
    let β := (SheafOfModules.tensorObjIsoSheafification B.toModule E) ≪≫ a
    have hT : ((SheafOfModules.siteSheafTensorRight E).obj B.toModule).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso β
        (quasiCoherent_tensor_product_affine_sections B.toModule E).1
    have hμtmul (U : X.Opens) (b : B.right.obj.obj (op U)) (s : E.val.obj (op U)) :
        μ.val.app (op U) (β.hom.val.app (op U) (tmulSection b s)) =
          @Mul.mul (B.right.obj.obj (op U)) inferInstance b (e.app U s) := by
      change μ.val.app (op U) (a.hom.val.app (op U) ((SheafOfModules.tensorObjIsoSheafification
        B.toModule E).hom.val.app (op U) (tmulSection b s))) = _
      rw [tmulSection]
      change μ.val.app (op U) (a.hom.val.app (op U)
        ((SheafOfModules.tensorObjIsoSheafification B.toModule E).hom.val.app (op U)
          ((SheafOfModules.tensorObjIsoSheafification B.toModule E).inv.val.app (op U)
            ((toSheafifyTensor B.toModule E).app (op U)
              (b ⊗ₜ[X.presheaf.obj (op U)] s))))) = _
      have hc : (SheafOfModules.tensorObjIsoSheafification B.toModule E).hom.val.app (op U)
          ((SheafOfModules.tensorObjIsoSheafification B.toModule E).inv.val.app (op U)
            ((toSheafifyTensor B.toModule E).app (op U)
              (b ⊗ₜ[X.presheaf.obj (op U)] s))) =
          (toSheafifyTensor B.toModule E).app (op U)
            (b ⊗ₜ[X.presheaf.obj (op U)] s) :=
        (appLinearEquivOfIso (SheafOfModules.tensorObjIsoSheafification
          B.toModule E) U).apply_symm_apply _
      have hn := congrArg (fun f ↦ f.app (op U) (b ⊗ₜ[X.presheaf.obj (op U)] s))
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
          c.hom)
      exact (congrArg (fun t ↦ μ.val.app (op U) (a.hom.val.app (op U) t)) hc).trans
        ((congrArg (μ.val.app (op U)) hn.symm).trans (hμ U b s))
    have : ((SheafOfModules.siteSheafTensorRight E).obj
        (commAlgebraSheafModule X.sheaf B)).IsQuasicoherent := hT
    have : (commAlgebraSheafModule X.toRingedSpace.sheaf B).IsQuasicoherent := hB
    have hci := quasiCoherent_cokernel_image μ
    let γ : image μ ≅ Abelian.image μ := (Abelian.imageIsoImage μ).symm
    have hγ : γ.hom ≫ Abelian.image.ι μ = image.ι μ := by
      exact (Iso.inv_comp_eq _).mpr (Abelian.imageIsoImage_hom_comp_image_ι μ).symm
    have hr (U : X.Opens) : Set.range ((image.ι μ).val.app (op U)) =
        Set.range ((Abelian.image.ι μ).val.app (op U)) := by
      have he := congrArg (fun f ↦ (f.val.app (op U) : _ → _)) hγ
      change (Abelian.image.ι μ).val.app (op U) ∘ γ.hom.val.app (op U) =
        ((image.ι μ).val.app (op U) : _ → _) at he
      rw [← he]
      exact (appLinearEquivOfIso γ U).surjective.range_comp _
    choose I hI using hideal
    have hIJ (U : X.Opens) : (I U : Set (B.right.obj.obj (op U))) =
        Set.range ((Abelian.image.ι μ).val.app (op U)) := (hI U).trans (hr U)
    have hIJker (U : X.Opens) (s : B.right.obj.obj (op U)) :
        s ∈ I U ↔ (cokernel.π μ).val.app (op U) s = 0 := by
      rw [show s ∈ I U ↔ s ∈ Set.range ((Abelian.image.ι μ).val.app (op U)) from
        Set.ext_iff.mp (hIJ U) s]
      exact Set.ext_iff.mp (range_map_kernelι U (cokernel.π μ)) s
    have hJ : (image μ : X.Modules).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso γ.symm
        hci.2.2.2.2.2.2.2.1
    have hinj (U : X.Opens) : Function.Injective ((image.ι μ).val.app (op U)) := by
      exact (ModuleCat.mono_iff_injective _).mp
        (show Mono ((image.ι μ).val.app (op U)) from
          inferInstanceAs (Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map
            (image.ι μ))))
    have hminimal' (K : X.Modules) (j : K ⟶ B.toModule)
        (L : ∀ U : X.Opens, Ideal (B.right.obj.obj (op U)))
        (hj : ∀ U : X.Opens, Function.Injective (j.app U) ∧
          Set.range (j.app U) = (L U : Set (B.right.obj.obj (op U))))
        (he : ∀ U : X.Opens, Set.range (e.app U) ⊆ (L U : Set (B.right.obj.obj (op U)))) :
        ∀ U : X.Opens, I U ≤ L U := by
      have hm : Mono j := ⟨fun f g h ↦ by
        ext W s
        apply (hj W).1
        exact congrArg (fun k ↦ k.val.app (op W) s) h⟩
      have hh := hminimal K j hm (fun U ↦ ⟨L U, (hj U).2.symm⟩)
        (fun U s ↦ (Set.ext_iff.mp (hj U).2 _).mpr (he U ⟨s, rfl⟩))
      intro U s hs
      exact (Set.ext_iff.mp (hj U).2 s).mp
        (hh U ((Set.ext_iff.mp (hI U) s).mp hs))
    have haff (U : X.Opens) (hU : IsAffineOpen U) :
        I U = Ideal.span (Set.range (e.app U) : Set (B.right.obj.obj (op U))) := by
      apply le_antisymm
      · intro z hz
        have hz' : z ∈ Set.range (μ.val.app (op U)) := by
          exact (Set.ext_iff.mp (hci.2.2.2.2.2.2.2.2 ⟨U, hU⟩).1 z).mp
            ((Set.ext_iff.mp (hIJ U) z).mp hz)
        obtain ⟨t, rfl⟩ := hz'
        obtain ⟨w, hw⟩ := (quasiCoherent_tensor_product_affine_sections B.toModule E).2
          U hU |>.2 ((appLinearEquivOfIso β U).symm t)
        have hw' : β.hom.val.app (op U) (tensorSectionsMap B.toModule E U w) = t := by
          rw [hw]
          exact (appLinearEquivOfIso β U).apply_symm_apply t
        rw [← hw']
        clear hw hw'
        induction w using TensorProduct.induction_on with
        | zero =>
          have hz0 : μ.val.app (op U) (β.hom.val.app (op U)
              (tensorSectionsMap B.toModule E U 0)) = 0 := by
            exact (congrArg (fun t ↦ μ.val.app (op U) (β.hom.val.app (op U) t))
              (tensorSectionsMap B.toModule E U).map_zero).trans
              ((congrArg (μ.val.app (op U)) ((β.hom.val.app (op U)).hom.map_zero)).trans
                ((μ.val.app (op U)).hom.map_zero))
          exact hz0.symm ▸ Ideal.zero_mem _
        | tmul b s =>
          rw [tensorSectionsMap_tmul, hμtmul]
          exact (Ideal.span (Set.range (e.app U) : Set (B.right.obj.obj (op U)))).mul_mem_left
            b (Ideal.subset_span ⟨s, rfl⟩)
        | add v w hv hw =>
          simp only [map_add]
          exact Ideal.add_mem _ hv hw
      · apply Ideal.span_le.mpr
        rintro _ ⟨s, rfl⟩
        exact (Set.ext_iff.mp (hI U) _).mpr (hcontains U s)
    let K : RingedSiteIdeal B.right :=
      { sections := I
        restriction := by
          intro U V f s hs
          apply (hIJker V _).mpr
          change (cokernel.π μ).val.app (op V) (B.toModule.val.map f.op s) = 0
          have hn := PresheafOfModules.naturality_apply (cokernel.π μ).val f.op s
          exact hn.trans (by rw [(hIJker U s).mp hs]; exact map_zero _)
        local_mem := by
          intro U s S hS hs
          apply (hIJker U s).mpr
          apply (cokernel μ).isSheaf.isSeparated _ _ hS
          intro V f hf
          change (cokernel μ).val.map f.op ((cokernel.π μ).val.app (op U) s) =
            (cokernel μ).val.map f.op 0
          rw [map_zero]
          exact (PresheafOfModules.naturality_apply (cokernel.π μ).val f.op s).symm.trans
            ((hIJker V _).mp (hs V f hf)) }
    let J : X.Modules := (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map
        B.hom)).obj K.module
    let i : J ⟶ B.toModule := algebraSheafIdealInclusion B K
    have hi (U : X.Opens) : Function.Injective (i.app U) ∧
        Set.range (i.app U) = (I U : Set (B.right.obj.obj (op U))) := by
      exact ⟨Subtype.val_injective, Subtype.range_val⟩
    have ε : (image μ : X.Modules) ≅ J := by
      let f : (image μ : X.Modules) ⟶ J :=
        { val :=
            { app := fun U ↦ ModuleCat.ofHom (X := (image μ).val.obj U) (Y := J.val.obj U)
                { toFun := fun t ↦ ⟨(image.ι μ).val.app U t,
                    (Set.ext_iff.mp (hI U.unop) _).mpr ⟨t, rfl⟩⟩
                  map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
                  map_smul' := fun r x ↦ by
                    apply Subtype.ext
                    exact ((image.ι μ).val.app U).hom.map_smul r x }
              naturality := by
                intro U V g
                apply ModuleCat.hom_ext
                apply LinearMap.ext
                intro t
                apply Subtype.ext
                exact PresheafOfModules.naturality_apply (image.ι μ).val g t } }
      have hf (U : X.Opens) : Function.Bijective (f.app U) := by
        constructor
        · intro x y hxy
          apply hinj U
          exact congrArg Subtype.val hxy
        · intro t
          obtain ⟨s, hs⟩ := (Set.ext_iff.mp (hI U) t.val).mp t.property
          exact ⟨s, Subtype.ext hs⟩
      let εp : (image μ).val ≅ J.val := PresheafOfModules.isoMk
        (fun U ↦ (LinearEquiv.ofBijective (f.val.app U).hom (hf U.unop)).toModuleIso)
        (by intro U V g; exact f.val.naturality g)
      exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso εp
    have hJ' : J.IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso ε hJ
    have hqci := quasiCoherent_cokernel_image i
    obtain ⟨⟨δ, hδ⟩, hlocal, huniv⟩ := algebraSheafQuotient_cokernel B K
    let Q : X.CommAlgebraSheaf := algebraSheafQuotient B K
    let q : B ⟶ Q := algebraSheafQuotientMap B K
    have hq (U : X.Opens) :
        δ.hom.val.app (op U) ∘ (cokernel.π i).val.app (op U) =
          (q.right.hom.app (op U) : _ → _) :=
      congrArg (fun f ↦ (f.val.app (op U) : _ → _)) hδ
    refine ⟨J, i, I, hJ', hi, ?_, hminimal', haff, ?_, ?_⟩
    · intro U s hs
      rw [hI U]
      obtain ⟨t, rfl⟩ := hs
      exact hcontains U t
    · refine ⟨a.hom ≫ μ, ?_, ?_⟩
      · intro U b s
        have hn := congrArg (fun f ↦ f.app (op U) (b ⊗ₜ[X.presheaf.obj (op U)] s))
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
            c.hom)
        exact (congrArg (μ.val.app (op U)) hn.symm).trans (hμ U b s)
      · intro U s
        apply (Set.ext_iff.mp (hIJ U) s).trans
        apply (hci.2.2.1 U s).trans
        have hrμ (V : X.Opens) : Set.range ((a.hom ≫ μ).val.app (op V)) =
            Set.range (μ.val.app (op V)) :=
          (appLinearEquivOfIso a V).surjective.range_comp _
        constructor
        · intro h x hx
          obtain ⟨V, hV, hxV, t, ht⟩ := h x hx
          refine ⟨V, hV, hxV, ?_⟩
          apply (Set.ext_iff.mp (hrμ V) _).mpr
          exact ⟨t, ht⟩
        · intro h x hx
          obtain ⟨V, hV, hxV, ht⟩ := h x hx
          obtain ⟨t, ht⟩ := (Set.ext_iff.mp (hrμ V) _).mp ht
          exact ⟨V, hV, hxV, t, ht⟩
    · refine ⟨Q, q, RingedSiteIdeal.ringQuotientPresheaf K,
        RingedSiteIdeal.ringQuotientPresheafProjection K, Iso.refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro U
        exact ⟨Ideal.Quotient.mk_surjective, Ideal.mk_ker⟩
      · simp only [Iso.refl_hom]
        rfl
      · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso δ
          hqci.2.2.2.2.2.2.1
      · intro U s x hx
        have := hlocal
        have hs := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
          (RingedSiteIdeal.ringProjection K).hom s
        rw [Opens.mem_grothendieckTopology] at hs
        obtain ⟨V, g, hg, hxV⟩ := hs x hx
        exact ⟨V, g.le, hxV, hg⟩
      · intro U hU
        have hs := (hqci.2.2.2.2.2.2.2.2 ⟨U, hU⟩).2
        constructor
        · rw [← hq U]
          exact (appLinearEquivOfIso δ U).surjective.comp hs.1
        · apply Ideal.ext
          intro b
          change q.right.hom.app (op U) b = 0 ↔ b ∈ I U
          rw [← hq U]
          change δ.hom.val.app (op U) ((cokernel.π i).app U b) = 0 ↔ b ∈ I U
          have hz : δ.hom.val.app (op U) ((cokernel.π i).app U b) = 0 ↔
              (cokernel.π i).app U b = 0 := by
            constructor
            · intro h
              exact (appLinearEquivOfIso δ U).injective
                (h.trans ((δ.hom.val.app (op U)).hom.map_zero).symm)
            · intro h
              exact (congrArg (δ.hom.val.app (op U)) h).trans
                ((δ.hom.val.app (op U)).hom.map_zero)
          have hk : (cokernel.π i).app U b = 0 ↔ b ∈ Set.range (i.app U) := by
            exact Set.ext_iff.mp
              (congrArg (fun M : Submodule (X.presheaf.obj (op U))
                (B.toModule.val.obj (op U)) ↦ (M : Set (B.toModule.val.obj (op U))))
                  hs.2.1) b
          exact hz.trans (hk.trans (Set.ext_iff.mp (hi U).2 b))
      · intro C χ hχ
        let χm : B.toModule ⟶ C.toModule := (commAlgebraSheafModuleFunctor X.sheaf).map χ
        have hmin := hminimal' (kernel χm) (kernel.ι χm)
          (fun U ↦ RingHom.ker (χ.right.hom.app (op U)).hom)
          (fun U ↦ ⟨injective_map_kernelι U χm, range_map_kernelι U χm⟩)
          (fun U _ hs ↦ by obtain ⟨t, rfl⟩ := hs; exact hχ U t)
        apply huniv C χ
        intro U b
        exact hmin U b.property

end AlgebraicGeometry.Scheme.CommAlgebraSheaf
