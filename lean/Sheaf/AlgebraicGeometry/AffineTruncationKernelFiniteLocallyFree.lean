/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat
import Sheaf.AlgebraicGeometry.PrincipalOpenFiniteProjectiveTilde
import Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Mathlib.Algebra.Category.ModuleCat.Images
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Finite local freeness of an affine truncation kernel

Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, proof of Lemma 36.13.6
(the DAG source calls this Tag 08ED)
(blueprint: lem-sc-affine-truncation-kernel-finite-locally-free).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem exactAt_of_tensor_vanish (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (i : ℤ)
    (h : ∀ G : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      schemeDerivedTensorCohomologyVanishes X
      (DerivedCategory.Q.obj C) G i) : C.ExactAt i := by
  let := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨R, _, ⟨e⟩, hz⟩ := h
    (MonoidalCategory.tensorUnit (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let t : CochainComplex.mapBifunctor R
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (MonoidalCategory.tensorUnit (SheafOfModules.{u} (moduleRings X.toRingedSpace))))
      (MonoidalCategory.curriedTensor _) ≅ R :=
    CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor _) _ R ≪≫
      (NatIso.mapHomologicalComplex
        (MonoidalCategory.rightUnitorNatIso
          (SheafOfModules.{u} (moduleRings X.toRingedSpace))) _).app R ≪≫
      (Functor.mapHomologicalComplexIdIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _).app R
  have hR : IsZero (R.homology i) :=
    hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso t).symm
  have hRC : R.homology i ≅ C.homology i :=
    ((DerivedCategory.homologyFunctorFactors _ i).app R).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app C
  exact (C.exactAt_iff_isZero_homology i).mpr (hR.of_iso hRC.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem image_kernel_of_exact {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk (F.map f) (F.map g) (by simp [← F.map_comp, hfg])).Exact) :
    ∃ e : F.obj (image f) ≅ kernel (F.map g),
      e.hom ≫ kernel.ι (F.map g) = F.map (image.ι f) := by
  let S := ShortComplex.mk (F.map f) (F.map g) (by simp [← F.map_comp, hfg])
  have hk := ((S.exact_iff_exact_image_ι).mp h).fIsKernel
  let e : F.obj (image f) ≅ kernel (F.map g) :=
    (PreservesImage.iso F f).symm ≪≫ (Abelian.imageIsoImage (F.map f)).symm ≪≫
      hk.conePointUniqueUpToIso (limit.isLimit _)
  refine ⟨e, ?_⟩
  dsimp [e]
  simp only [Category.assoc]
  have hh : (hk.conePointUniqueUpToIso (limit.isLimit _)).hom ≫
      kernel.ι (F.map g) = Abelian.image.ι (F.map f) :=
    IsLimit.conePointUniqueUpToIso_hom_comp hk (limit.isLimit _) WalkingParallelPair.zero
  rw [hh]
  have ha : (Abelian.imageIsoImage (F.map f)).inv ≫ Abelian.image.ι (F.map f) =
      image.ι (F.map f) := by
    change (Abelian.imageIsoImage (F.map f)).inv ≫ kernel.ι _ = _
    rw [Abelian.imageIsoImage_inv]
    exact kernel.lift_ι _ _ _
  rw [ha]
  exact PreservesImage.inv_comp_image_ι_map F f

-- A categorical generalization of the private affine finite-limit helper.
private theorem preservesFiniteLimits_of_kernel_in_essentialImage
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.Full] [T.Faithful] [T.Additive]
    (hkernel : ∀ {M N : C} (f : M ⟶ N),
      ∃ K : C, Nonempty (T.obj K ≅ kernel (T.map f))) : PreservesFiniteLimits T := by
  let : ∀ {M N : C} (f : M ⟶ N), PreservesLimit (parallelPair f 0) T := by
    intro M N f
    obtain ⟨K, ⟨e⟩⟩ := hkernel f
    let t := T.preimage (e.hom ≫ kernel.ι (T.map f))
    have ht : t ≫ f = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, kernel.condition, comp_zero, t]
    let c := KernelFork.ofι t ht
    have hc : IsLimit (c.map T) := by
      apply IsLimit.ofIsoLimit (kernelIsKernel (T.map f))
      exact Fork.ext e.symm (by simp [c, t, KernelFork.map])
    have hc' : IsLimit c :=
      isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  exact Functor.preservesFiniteLimits_of_preservesKernels _


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
-- The derived restriction and image comparisons need extra definitional-equality reduction.
/-- Below the Tor-amplitude bound, the image of the preceding differential restricts to
its successor's kernel, and is flat, finitely presented and finite locally free on U.
The kernel/image assertion is only on U, never on the entire affine scheme.
Source: Stacks Project, Tag 08EG, proof of Lemma 36.13.6
(blueprint: lem-sc-affine-truncation-kernel-finite-locally-free).

Proof:
1. Test tensor vanishing with the tensor unit and use the right unitor to obtain
   ordinary homology vanishing of the restricted complex in degree r. Exactness
   and preservation of images identify the restricted image with the next kernel,
   with the required compatibility with the kernel inclusion.
2. Compare termwise restriction followed by Q with the derived restriction of
   the termwise tilde complex. Transport Tor vanishing along this comparison and
   apply lem-sc-affine-truncation-kernel-flat on each principal open inside U.
3. Each localized image is finitely presented and flat, hence finite projective
   by Mathlib's Tag 00NX theorem. Apply
   lem-sc-principal-open-finite-projective-tilde to the linear range module and
   transport local freeness through ModuleCat.imageIsoRange.
4. Finite locally free sheaves have finite presentation. The tensor-exactness
   theorem lem-sc-ext-tensor-exact and the braiding prove right tensor exactness,
   which is the stated sheaf flatness. -/
theorem affine_truncationKernel_finiteLocallyFree (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) (hU : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hbounded : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i) ∧ Module.Finite A (P.X i))
    (E : schemeDerivedCategory U.toScheme) (hperfect : Scheme.IsPerfect U.toScheme E)
    (hrep : Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ _ _
          ((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
            SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv U))
          ⟨fun _ _ ↦ by simp⟩ (ComplexShape.up ℤ)).obj P) ≅ E))
    (a b : ℤ) (hab : a ≤ b)
    (htor : ∀ G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes U.toScheme E G i)
    (r : ℤ) (hr : r < a) :
    (∃ e : ((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r)) ≅
      kernel (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).map (P.d r (r + 1))),
      e.hom ≫ kernel.ι (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).map (P.d r (r + 1))) =
        ((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).map (image.ι (P.d (r - 1) r))) ∧
    SheafOfModules.IsFlat (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r))) ∧
    SheafOfModules.IsFinitePresentation (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r))) ∧
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r))) := by
  have _ := hperfect
  have _ := hab
  let F := (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⋙
    SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
    (Scheme.Modules.overEquiv U).functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ by simp [F]⟩
  let : (tilde.functor (.of A)).IsLeftAdjoint :=
    (tilde.adjunction (R := .of A)).isLeftAdjoint
  let : PreservesFiniteColimits (tilde.functor (.of A)) := inferInstance
  let ff := tilde.fullyFaithfulFunctor (R := .of A)
  let : (tilde.functor (.of A)).Full := ff.full
  let : (tilde.functor (.of A)).Faithful := ff.faithful
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor (.of A))
  let : (tilde.functor (.of A)).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  let : PreservesFiniteLimits (tilde.functor (.of A)) :=
    preservesFiniteLimits_of_kernel_in_essentialImage _ (by
      intro M N f
      have : ((tilde.functor (.of A)).obj M).IsQuasicoherent := by
        change (tilde.{u} (R := .of A) M).IsQuasicoherent
        infer_instance
      have : ((tilde.functor (.of A)).obj N).IsQuasicoherent := by
        change (tilde.{u} (R := .of A) N).IsQuasicoherent
        infer_instance
      let k := kernel ((tilde.functor (.of A)).map f)
      have : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel _
      have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
        Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
      exact ⟨(moduleSpecΓFunctor (R := .of A)).obj k,
        ⟨asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)⟩⟩)
  let : PreservesFiniteLimits F := by
    dsimp only [F, id]
    exact comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := by
    dsimp only [F, id]
    exact comp_preservesFiniteColimits _ _
  let : F.Additive := Functor.additive_of_preserves_binary_products _
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  obtain ⟨e⟩ := hrep
  have hvan (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (i : ℤ) (hi : i < a ∨ b < i) :
      schemeDerivedTensorCohomologyVanishes U.toScheme
        (DerivedCategory.Q.obj C) G i := by
    obtain ⟨R, hR, ⟨eR⟩, hz⟩ := htor G i hi
    exact ⟨R, hR, ⟨eR ≪≫ e.symm⟩, hz⟩
  have hex : C.ExactAt r := exactAt_of_tensor_vanish U.toScheme C r
    (fun G ↦ hvan G r (Or.inl hr))
  have hshort : (ShortComplex.mk (F.map (P.d (r - 1) r))
      (F.map (P.d r (r + 1))) (by simp [← F.map_comp])).Exact := by
    exact ShortComplex.exact_of_iso
      (C.isoSc' (r - 1) r (r + 1) (by simp) (by simp))
      ((C.exactAt_iff r).mp hex)
  have himage := image_kernel_of_exact F (P.d (r - 1) r) (P.d r (r + 1))
    (P.d_comp_d _ _ _) hshort
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) :=
    HasDerivedCategory.standard _
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  let R : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
    (Scheme.Modules.overEquiv U).functor
  let : R.PreservesZeroMorphisms := ⟨fun _ _ ↦ by simp [R]⟩
  let : PreservesFiniteLimits R := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits R := comp_preservesFiniteColimits _ _
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : PreservesFiniteLimits T := inferInstance
  let : T.Additive := Functor.additive_of_preserves_binary_products _
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let eC : R.mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj C :=
    R.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (T ⋙ R)) (.up ℤ)).app P)
  have hlocal := affine_truncation_kernel_flat A P hbounded hfree U hU a b r hr
    (fun G i hi ↦ by
      obtain ⟨K, hK, ⟨eK⟩, hz⟩ := hvan G i hi
      exact ⟨K, hK, ⟨eK ≪≫ eC.symm⟩, hz⟩)
  have hproj (f : A) (hf : PrimeSpectrum.basicOpen f ≤ U) :
      Module.Finite (Localization.Away f)
          (LocalizedModule.Away f (LinearMap.range (P.d (r - 1) r).hom)) ∧
        Module.Projective (Localization.Away f)
          (LocalizedModule.Away f (LinearMap.range (P.d (r - 1) r).hom)) := by
    obtain ⟨hflat, hfp⟩ := hlocal f hf
    have := hflat
    have := hfp
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
  have hfreeRange := finiteLocallyFree_restrict_tilde_of_principalOpen_projective
    A U (ModuleCat.of A (LinearMap.range (P.d (r - 1) r).hom)) hproj
  have hfl : (F.obj (image (P.d (r - 1) r))).IsFiniteLocallyFree := by
    have : (F.obj (ModuleCat.of A
        (LinearMap.range (P.d (r - 1) r).hom))).IsFiniteLocallyFree := hfreeRange
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
      (R := U.toScheme.ringCatSheaf)
      (F.mapIso (ModuleCat.imageIsoRange (P.d (r - 1) r))).symm
  have := hfl
  have hfp : (F.obj (image (P.d (r - 1) r))).IsFinitePresentation := inferInstance
  have hf : SheafOfModules.IsFlat (F.obj (image (P.d (r - 1) r))) := by
    let := SheafOfModules.monoidalCategory U.toScheme.sheaf
    let := SheafOfModules.symmetricCategory U.toScheme.sheaf
    obtain ⟨hl, hc⟩ := Scheme.Modules.finiteLocallyFree_tensorLeft_exact
      (X := U.toScheme)
      (F.obj (image (P.d (r - 1) r)))
    have : PreservesFiniteLimits
        (MonoidalCategory.tensorLeft (F.obj (image (P.d (r - 1) r)))) := hl
    have : PreservesFiniteColimits
        (MonoidalCategory.tensorLeft (F.obj (image (P.d (r - 1) r)))) := hc
    let t := BraidedCategory.tensorLeftIsoTensorRight
      (F.obj (image (P.d (r - 1) r)))
    exact ⟨@preservesFiniteLimits_of_natIso _ _ _ _ _ _ t hl,
      @preservesFiniteColimits_of_natIso _ _ _ _ _ _ t hc⟩
  exact ⟨himage, hf, hfp, hfl⟩

end AlgebraicGeometry
