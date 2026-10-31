/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeScalarCalculusData
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Normalized finite-free scalar constructions

Source: Stacks Project, Tags 03CZ, 05V4, 06YU and 05RT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory WeilConjectures

namespace AlgebraicGeometry

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  [Algebra A B] (r : ℕ) (basis : Module.Basis (Fin r) A B)

include basis in
private theorem scalarExtension_limits :
    PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B)) := by
  have : Module.Free A B := Module.Free.of_basis basis
  have : Module.Finite A B := Module.Finite.of_basis basis
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat A B))
  have : PreservesFiniteLimits ((Functor.whiskeringRight Cᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B))) := by
    constructor
    intro D _ _
    infer_instance
  unfold finiteScalarExtension Sheaf.composeAndSheafify
  exact comp_preservesFiniteLimits _ _

private instance scalarExtension_colimits :
    PreservesFiniteColimits (finiteScalarExtension J (algebraMap A B)) := by
  have := (finiteScalarAdjunction J (algebraMap A B)).leftAdjoint_preservesColimits
  infer_instance

private theorem scalarOrdinaryBasis (M : Sheaf J (ModuleCat.{u + 1} A)) :
    IsIso (biproduct.desc fun j : Fin r ↦
      (finiteScalarAdjunction J (algebraMap A B)).unit.app M ≫
        (Sheaf.restrictScalars J (algebraMap A B)).map (basis j • 𝟙 _)) := by
  have : Module.Free A B := Module.Free.of_basis basis
  have : Module.Finite A B := Module.Finite.of_basis basis
  let φ := algebraMap A B
  let b' := basis.map ModuleCat.restrictScalarsAlgebraMapSelfLinearEquiv.{u}
  have : PreservesLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) :=
    ModuleCat.preservesLimits_extendScalars_of_finite_projective φ
      (by rw [toAlgebra_algebraMap]; infer_instance)
      (by rw [toAlgebra_algebraMap]; infer_instance)
  have hs : Presheaf.IsSheaf J
      (M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) :=
    ((sheafCompose J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj M).property
  have : IsIso (toSheafify J (M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)) :=
    isIso_toSheafify _ hs
  have hV (V : Cᵒᵖ) : IsIso (biproduct.desc fun j : Fin r ↦
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app (M.obj.obj V) ≫
        (ModuleCat.restrictScalars.{u + 1} φ).map
          (ModuleCat.restrictScalarsSelfVal φ (b' j) • 𝟙 _)) :=
    ModuleCat.ExtendScalars.isIso_biproductDesc_unit_comp_map_smul φ b' (M.obj.obj V)
  let t := Functor.whiskerRight
    (toSheafify J (M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
    (ModuleCat.restrictScalars.{u + 1} φ)
  let ψ (j : Fin r) :=
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).whiskerRight Cᵒᵖ).unit.app
      M.obj ≫ Functor.whiskerRight
        (basis j • 𝟙 (M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
        (ModuleCat.restrictScalars.{u + 1} φ)
  have hψ : IsIso (biproduct.desc ψ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    have : IsIso (biproduct.desc fun j ↦ ((evaluation _ _).obj V).map (ψ j)) := hV V
    exact Functor.isIso_map_biproductDesc ((evaluation _ _).obj V) ψ
  have he : (biproduct.desc fun j : Fin r ↦ (sheafToPresheaf J _).map
      ((finiteScalarAdjunction J φ).unit.app M ≫
        (Sheaf.restrictScalars J φ).map (basis j • 𝟙 _))) =
      biproduct.desc ψ ≫ t := by
    apply biproduct.hom_ext'
    intro j
    simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, Functor.map_comp]
    change ((Sheaf.adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).unit.app M).hom ≫
      Functor.whiskerRight
        (basis j • 𝟙 ((finiteScalarExtension J φ).obj M)).hom
          (ModuleCat.restrictScalars.{u + 1} φ) = _
    rw [Sheaf.adjunction_unit_app_hom]
    simp only [ψ, t, Category.assoc, ← Functor.whiskerRight_comp]
    congr 2
    change toSheafify _ _ ≫ (basis j • 𝟙 _) = (basis j • 𝟙 _) ≫ toSheafify _ _
    rw [Linear.comp_smul, Linear.smul_comp]
    erw [Category.comp_id]
  have : IsIso (biproduct.desc fun j : Fin r ↦ (sheafToPresheaf J _).map
      ((finiteScalarAdjunction J φ).unit.app M ≫
        (Sheaf.restrictScalars J φ).map (basis j • 𝟙 _))) := by
    have : IsIso (biproduct.desc ψ ≫ t) := inferInstance
    exact he.symm ▸ this
  have := Functor.isIso_map_biproductDesc (sheafToPresheaf J _)
    (φ := fun j : Fin r ↦ (finiteScalarAdjunction J φ).unit.app M ≫
      (Sheaf.restrictScalars J φ).map (basis j • 𝟙 _))
  exact isIso_of_reflects_iso _ (sheafToPresheaf J _)

private def scalarDerivedAdj
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))] :
    (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory ⊣
      Sheaf.derivedRestrictScalars J (algebraMap A B) := by
  let E := finiteScalarExtension J (algebraMap A B)
  let U := Sheaf.restrictScalars J (algebraMap A B)
  letI : CatCommSq (E.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q E.mapDerivedCategory := ⟨E.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (U.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q U.mapDerivedCategory := ⟨U.mapDerivedCategoryFactors.symm⟩
  exact ((finiteScalarAdjunction J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    E.mapDerivedCategory U.mapDerivedCategory

private theorem scalarDerivedAdj_unit
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (scalarDerivedAdj J (B := B)).unit.app (DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars J (algebraMap A B)).map
        ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategoryFactors.hom.app P) ≫
      (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategoryFactors.hom.app
        (((finiteScalarExtension J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (finiteScalarAdjunction J (algebraMap A B)).unit (.up ℤ)).app P) := by
  change _ = DerivedCategory.Q.map
    (((finiteScalarAdjunction J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).unit.app P)
  simp only [scalarDerivedAdj, Adjunction.localization_unit_app]
  simp only [Sheaf.derivedRestrictScalars, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  erw [Iso.inv_hom_id_app, Category.comp_id]

private theorem scalarDerivedAdj_counit
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    (Q : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ) :
    (scalarDerivedAdj J (B := B)).counit.app (DerivedCategory.Q.obj Q) =
      (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.map
        ((Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategoryFactors.hom.app Q) ≫
      (finiteScalarExtension J (algebraMap A B)).mapDerivedCategoryFactors.hom.app
        (((Sheaf.restrictScalars J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (finiteScalarAdjunction J (algebraMap A B)).counit (.up ℤ)).app Q) := by
  simp only [scalarDerivedAdj, Adjunction.localization_counit_app, CatCommSq.iso,
    Iso.symm_inv]
  rfl

private theorem scalarBasisComponent_natural
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    {K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))} (f : K ⟶ L) (j : Fin r) :
    f ≫ (scalarDerivedAdj J (B := B)).unit.app L ≫
        (Sheaf.derivedRestrictScalars J (algebraMap A B)).map (basis j • 𝟙 _) =
      (scalarDerivedAdj J (B := B)).unit.app K ≫
        (Sheaf.derivedRestrictScalars J (algebraMap A B)).map (basis j • 𝟙 _) ≫
        (Sheaf.derivedRestrictScalars J (algebraMap A B)).map
          ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.map f) := by
  let E := (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory
  let U := Sheaf.derivedRestrictScalars J (algebraMap A B)
  have hn := (scalarDerivedAdj J (B := B)).unit.naturality f
  change f ≫ (scalarDerivedAdj J (B := B)).unit.app L =
    (scalarDerivedAdj J (B := B)).unit.app K ≫ U.map (E.map f) at hn
  rw [reassoc_of% hn]
  change (scalarDerivedAdj J (B := B)).unit.app K ≫
      U.map (E.map f) ≫ U.map (basis j • 𝟙 _) =
    (scalarDerivedAdj J (B := B)).unit.app K ≫
      U.map (basis j • 𝟙 _) ≫ U.map (E.map f)
  rw [← U.map_comp, ← U.map_comp]
  congr 2
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
  erw [Category.comp_id]

private theorem scalarDerivedBasis
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    IsIso (biproduct.desc fun j : Fin r ↦ (scalarDerivedAdj J (B := B)).unit.app K ≫
      (Sheaf.derivedRestrictScalars J (algebraMap A B)).map (basis j • 𝟙 _)) := by
  let E := finiteScalarExtension J (algebraMap A B)
  let U := Sheaf.restrictScalars J (algebraMap A B)
  let adj := finiteScalarAdjunction J (algebraMap A B)
  have hC (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
      IsIso (biproduct.desc fun j : Fin r ↦
        (adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
          (U.mapHomologicalComplex (.up ℤ)).map (basis j • 𝟙 _)) := by
    have (n : ℤ) : IsIso ((biproduct.desc fun j : Fin r ↦
        (adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
          (U.mapHomologicalComplex (.up ℤ)).map (basis j • 𝟙 _)).f n) := by
      have he : (fun j : Fin r ↦ (HomologicalComplex.eval _ _ n).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
            (U.mapHomologicalComplex (.up ℤ)).map (basis j • 𝟙 _))) =
          fun j : Fin r ↦ adj.unit.app (P.X n) ≫ U.map (basis j • 𝟙 _) := by
        ext j
        simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f,
          Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
          HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
        rfl
      have : IsIso (biproduct.desc fun j : Fin r ↦ (HomologicalComplex.eval _ _ n).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
            (U.mapHomologicalComplex (.up ℤ)).map (basis j • 𝟙 _))) := by
        rw [he]
        exact scalarOrdinaryBasis J r basis (P.X n)
      exact Functor.isIso_map_biproductDesc (HomologicalComplex.eval _ _ n) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
      IsIso (biproduct.desc fun j : Fin r ↦
        (scalarDerivedAdj J (B := B)).unit.app (DerivedCategory.Q.obj P) ≫
          U.mapDerivedCategory.map (basis j • 𝟙 _)) := by
    have := hC P
    have := Functor.isIso_biproductDesc_map DerivedCategory.Q
      (fun j : Fin r ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (U.mapHomologicalComplex (.up ℤ)).map (basis j • 𝟙 _))
    refine isIso_biproductDesc_of_iso _
      (fun j : Fin r ↦ DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
          (U.mapHomologicalComplex (.up ℤ)).map (basis j • 𝟙 _))) (Iso.refl _)
      (U.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app P) ≪≫
        U.mapDerivedCategoryFactors.app _) (fun j ↦ ?_) this
    have hfac : (scalarDerivedAdj J (B := B)).unit.app (DerivedCategory.Q.obj P) ≫
        U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app P) ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) :=
      scalarDerivedAdj_unit J (B := B) P
    have he₁ : (basis j • 𝟙 (E.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ≫
        E.mapDerivedCategoryFactors.hom.app P =
      E.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (basis j • 𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
        Category.id_comp]
      erw [Category.comp_id]
    have he₂ := U.mapDerivedCategoryFactors.hom.naturality
      (basis j • 𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj P))
    simp only [Functor.comp_map] at he₂
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom,
      Category.id_comp, Category.assoc, Functor.map_comp]
    rw [← reassoc_of% hfac, ← U.mapDerivedCategory.map_comp_assoc, he₁,
      U.mapDerivedCategory.map_comp_assoc]
    congr 2
  let e := DerivedCategory.Q.objObjPreimageIso K
  refine isIso_biproductDesc_of_iso _ _ e.symm
    ((E.mapDerivedCategory ⋙ U.mapDerivedCategory).mapIso e.symm) (fun j ↦ ?_)
    (hQ (DerivedCategory.Q.objPreimage K))
  simpa only [Functor.mapIso_hom, Iso.symm_hom, Functor.comp_map, Category.assoc]
    using (scalarBasisComponent_natural J r basis e.inv j).symm

private theorem scalarDerived_reflects_iso :
    (Sheaf.derivedRestrictScalars J (algebraMap A B)).ReflectsIsomorphisms where
  reflects f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((Sheaf.restrictScalars J (algebraMap A B)).map
        ((DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff
        ((Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategoryHomologyFunctorIso n)
        f).2 (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (Sheaf.restrictScalars J (algebraMap A B))

private theorem scalarDerived_reflects_zero
    (N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (hN : IsZero ((Sheaf.derivedRestrictScalars J (algebraMap A B)).obj N)) :
    IsZero N := by
  apply (DerivedCategory.isZero_iff N).2
  intro n
  exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (Sheaf.restrictScalars J (algebraMap A B)) ((DerivedCategory.isZero_iff _).1 hN n)

private def scalarBasisIso
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    (Sheaf.derivedRestrictScalars J (algebraMap A B)).obj
      ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.obj K) ≅
        ⨁ (fun _j : Fin r ↦ K) := by
  have := scalarDerivedBasis J r basis K
  exact (asIso (biproduct.desc fun j : Fin r ↦ (scalarDerivedAdj J (B := B)).unit.app K ≫
    (Sheaf.derivedRestrictScalars J (algebraMap A B)).map (basis j • 𝟙 _))).symm

private theorem scalarBasisIso_inclusion
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) (j : Fin r) :
    biproduct.ι (fun _j : Fin r ↦ K) j ≫ (scalarBasisIso J r basis K).inv =
      (scalarDerivedAdj J (B := B)).unit.app K ≫
        (Sheaf.derivedRestrictScalars J (algebraMap A B)).map (basis j • 𝟙 _) := by
  exact biproduct.ι_desc _ _

private theorem scalarBasisIso_natural
    [PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
    {K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))} (f : K ⟶ L) :
    (Sheaf.derivedRestrictScalars J (algebraMap A B)).map
        ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.map f) ≫
      (scalarBasisIso J r basis L).hom =
        (scalarBasisIso J r basis K).hom ≫ biproduct.map (fun _j : Fin r ↦ f) := by
  let E := (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory
  let U := Sheaf.derivedRestrictScalars J (algebraMap A B)
  have h : biproduct.map (fun _j : Fin r ↦ f) ≫ (scalarBasisIso J r basis L).inv =
      (scalarBasisIso J r basis K).inv ≫ U.map (E.map f) := by
    apply biproduct.hom_ext'
    intro j
    rw [biproduct.ι_map_assoc, scalarBasisIso_inclusion,
      reassoc_of% scalarBasisIso_inclusion J r basis K j]
    simpa only [Category.assoc] using scalarBasisComponent_natural J r basis f j
  apply (cancel_epi (scalarBasisIso J r basis K).inv).1
  apply (cancel_mono (scalarBasisIso J r basis L).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id, Category.id_comp] using h.symm

private def scalarDescent
    (hKflat : ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((finiteScalarExtension J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj P)) :
    FiniteFreeScalarDescent J r basis := by
  letI := scalarExtension_limits J r basis
  exact {
    extension_limits := inferInstance
    extension_colimits := inferInstance
    restriction_limits := inferInstance
    restriction_colimits := inferInstance
    universal := Functor.isLeftDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso _ (.up ℤ)) _
      (finiteScalarExtension J (algebraMap A B)).mapDerivedCategoryFactors
    adjunction := scalarDerivedAdj J
    unit_normalized := scalarDerivedAdj_unit J
    counit_normalized := scalarDerivedAdj_counit J
    reflects_iso := scalarDerived_reflects_iso J
    reflects_zero := scalarDerived_reflects_zero J
    basis_iso := scalarBasisIso J r basis
    basis_natural := scalarBasisIso_natural J r basis
    basis_inclusion := scalarBasisIso_inclusion J r basis
    kflat_extension := hKflat }

private def tensorSheafify (R : Type (u + 1)) [CommRing R]
    (M N : Sheaf J (ModuleCat.{u + 1} R)) :
    M ⊗ N ≅ (presheafToSheaf J (ModuleCat.{u + 1} R)).obj (M.obj ⊗ N.obj) :=
  tensorIso ((asIso (sheafificationAdjunction J _).counit).app M).symm
    ((asIso (sheafificationAdjunction J _).counit).app N).symm ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J _) M.obj N.obj

private theorem tensorSheafify_fac (R : Type (u + 1)) [CommRing R]
    (M N : Sheaf J (ModuleCat.{u + 1} R)) :
    Functor.LaxMonoidal.μ (sheafToPresheaf J _) M N ≫
      (tensorSheafify J R M N).hom.hom = toSheafify J (M.obj ⊗ N.obj) := by
  have hμ : Functor.LaxMonoidal.μ (sheafToPresheaf J _) M N =
      toSheafify J (M.obj ⊗ N.obj) ≫ (tensorSheafify J R M N).inv.hom := rfl
  rw [hμ, Category.assoc, ObjectProperty.isoInv_hom_id_hom, Category.comp_id]


private instance scalarRawLimits [Module.Free A B] [Module.Finite A B] :
    PreservesLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) :=
  ModuleCat.preservesLimits_extendScalars_of_finite_projective (algebraMap A B)
    (by rw [toAlgebra_algebraMap]; infer_instance)
    (by rw [toAlgebra_algebraMap]; infer_instance)

private def scalarRawExtensionIso [Module.Free A B] [Module.Finite A B]
    (M : Sheaf J (ModuleCat.{u + 1} A)) :
    M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B) ≅
      ((finiteScalarExtension J (algebraMap A B)).obj M).obj := by
  have hs : Presheaf.IsSheaf J
      (M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) :=
    ((sheafCompose J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B))).obj M).property
  have := isIso_toSheafify J hs
  exact asIso (toSheafify J _)

private def rawBalance (M : Cᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (N : Cᵒᵖ ⥤ ModuleCat.{u + 1} B) :
    ((M ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) ⊗ N) ⋙
        ModuleCat.restrictScalars.{u + 1} (algebraMap A B) ≅
      M ⊗ (N ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) :=
  ((Functor.whiskeringRight Cᵒᵖ _ _).obj
      (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))).mapIso
      (β_ (M ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) N) ≪≫
    (Presheaf.tensorRightExtendScalarsCompRestrictScalarsIso
      (algebraMap A B) M).app N ≪≫
    β_ (N ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) M

omit [EssentiallySmall.{u + 1} C] in
private theorem rawBalance_pure (M : Cᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (N : Cᵒᵖ ⥤ ModuleCat.{u + 1} B) (V : Cᵒᵖ)
    (m : M.obj V) (b : B) (n : N.obj V) :
    (rawBalance M N).hom.app V ((b ⊗ₜ[A] m) ⊗ₜ[B] n) =
      TensorProduct.tmul A (M := M.obj V)
        (N := (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)).obj (N.obj V)) m (b • n) := rfl

omit [EssentiallySmall.{u + 1} C] in
private theorem rawBalance_natural
    {M M' : Cᵒᵖ ⥤ ModuleCat.{u + 1} A}
    {N N' : Cᵒᵖ ⥤ ModuleCat.{u + 1} B} (f : M ⟶ M') (g : N ⟶ N') :
    Functor.whiskerRight (Functor.whiskerRight f
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) ⊗ₘ g)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) ≫ (rawBalance M' N').hom =
      (rawBalance M N).hom ≫
        (f ⊗ₘ Functor.whiskerRight g (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))) := by
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
  have hc : W.map (g ⊗ₘ Functor.whiskerRight f
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B))) ≫
      ((Presheaf.tensorRightExtendScalarsCompRestrictScalarsIso
        (algebraMap A B) M').app N').hom =
      ((Presheaf.tensorRightExtendScalarsCompRestrictScalarsIso
        (algebraMap A B) M).app N).hom ≫
        (Functor.whiskerRight g (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) ⊗ₘ f) := by
    ext V : 2
    exact ModuleCat.restrictScalarsTensorExtendScalarsIso_hom_naturality
      (algebraMap A B) (g.app V) (f.app V)
  change W.map _ ≫ (W.map _ ≫ _ ≫ _) = (W.map _ ≫ _ ≫ _) ≫ _
  rw [← W.map_comp_assoc, BraidedCategory.braiding_naturality, W.map_comp_assoc,
    reassoc_of% hc, BraidedCategory.braiding_naturality]
  simp only [Category.assoc]
  rfl

private theorem tensorSheafify_natural (R : Type (u + 1)) [CommRing R]
    {M M' N N' : Sheaf J (ModuleCat.{u + 1} R)} (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (tensorSheafify J R M' N').hom =
      (tensorSheafify J R M N).hom ≫
        (presheafToSheaf J (ModuleCat.{u + 1} R)).map (f.hom ⊗ₘ g.hom) := by
  let e := asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit
  have hf : f ≫ (e.app M').inv =
      (e.app M).inv ≫ (presheafToSheaf J _).map f.hom := e.inv.naturality f
  have hg : g ≫ (e.app N').inv =
      (e.app N).inv ≫ (presheafToSheaf J _).map g.hom := e.inv.naturality g
  change (f ⊗ₘ g) ≫ ((e.app M').inv ⊗ₘ (e.app N').inv) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J _) M'.obj N'.obj =
    (((e.app M).inv ⊗ₘ (e.app N).inv) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J _) M.obj N.obj) ≫ _
  rw [tensorHom_comp_tensorHom_assoc, hf, hg, ← tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, Functor.LaxMonoidal.μ_natural]
  rfl


private def scalarBalance [Module.Free A B] [Module.Finite A B]
    (M : Sheaf J (ModuleCat.{u + 1} A)) (N : Sheaf J (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars J (algebraMap A B)).obj
        (((finiteScalarExtension J (algebraMap A B)).obj M) ⊗ N) ≅
      M ⊗ (Sheaf.restrictScalars J (algebraMap A B)).obj N := by
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  let U := Sheaf.restrictScalars J (algebraMap A B)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
  let e : W.obj (((finiteScalarExtension J (algebraMap A B)).obj M).obj ⊗ N.obj) ≅
      M.obj ⊗ (U.obj N).obj :=
    W.mapIso (tensorIso (scalarRawExtensionIso J (B := B) M).symm (Iso.refl N.obj)) ≪≫
      rawBalance M.obj N.obj
  exact U.mapIso (tensorSheafify J B _ N) ≪≫
    ((sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
      (sheafificationAdjunction J (ModuleCat.{u + 1} B))
      (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm.app
        (((finiteScalarExtension J (algebraMap A B)).obj M).obj ⊗ N.obj)) ≪≫
    (presheafToSheaf J (ModuleCat.{u + 1} A)).mapIso e ≪≫
    (tensorSheafify J A M (U.obj N)).symm

private theorem scalarBalance_fac [Module.Free A B] [Module.Finite A B]
    (M : Sheaf J (ModuleCat.{u + 1} A)) (N : Sheaf J (ModuleCat.{u + 1} B)) :
    Functor.whiskerRight
        (Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{u + 1} B))
          ((finiteScalarExtension J (algebraMap A B)).obj M) N)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) ≫ (scalarBalance J M N).hom.hom =
      Functor.whiskerRight
          ((scalarRawExtensionIso J (B := B) M).inv ⊗ₘ 𝟙 N.obj)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) ≫ (rawBalance M.obj N.obj).hom ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{u + 1} A))
          M ((Sheaf.restrictScalars J (algebraMap A B)).obj N) := by
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  let U := Sheaf.restrictScalars J (algebraMap A B)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
  let EM := (finiteScalarExtension J (algebraMap A B)).obj M
  let qB := tensorSheafify J B EM N
  let qA := tensorSheafify J A M (U.obj N)
  let c := (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
    (sheafificationAdjunction J (ModuleCat.{u + 1} B))
    (sheafificationAdjunction J (ModuleCat.{u + 1} A))).app (EM.obj ⊗ N.obj)
  let e : W.obj (EM.obj ⊗ N.obj) ≅ M.obj ⊗ (U.obj N).obj :=
    W.mapIso (tensorIso (scalarRawExtensionIso J (B := B) M).symm (Iso.refl N.obj)) ≪≫
      rawBalance M.obj N.obj
  have h₁ : W.map (Functor.LaxMonoidal.μ (sheafToPresheaf J _) EM N) ≫
      (U.map qB.hom).hom = W.map (toSheafify J (EM.obj ⊗ N.obj)) := by
    change W.map _ ≫ W.map qB.hom.hom = _
    simpa only [Functor.map_comp] using W.congr_map (tensorSheafify_fac J B EM N)
  have h₂ : W.map (toSheafify J (EM.obj ⊗ N.obj)) ≫ c.inv.hom =
      toSheafify J (W.obj (EM.obj ⊗ N.obj)) :=
    sheafComposeIso_inv_fac J (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) _
  have h₃ : toSheafify J (W.obj (EM.obj ⊗ N.obj)) ≫
      ((presheafToSheaf J _).map e.hom).hom =
        e.hom ≫ toSheafify J (M.obj ⊗ (U.obj N).obj) :=
    ((sheafificationAdjunction J _).unit.naturality e.hom).symm
  have h₄ : toSheafify J (M.obj ⊗ (U.obj N).obj) ≫ qA.inv.hom =
      Functor.LaxMonoidal.μ (sheafToPresheaf J _) M (U.obj N) := by
    rw [← tensorSheafify_fac J A M (U.obj N)]
    change _ ≫ qA.hom.hom ≫ qA.inv.hom = _
    rw [ObjectProperty.isoHom_inv_id_hom, Category.comp_id]
  have hf : W.map (Functor.LaxMonoidal.μ (sheafToPresheaf J _) EM N) ≫
      ((U.map qB.hom).hom ≫ c.inv.hom ≫
        ((presheafToSheaf J _).map e.hom).hom ≫ qA.inv.hom) =
      e.hom ≫ Functor.LaxMonoidal.μ (sheafToPresheaf J _) M (U.obj N) := by
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simpa only [scalarBalance, e, qA, qB, c, U, W, EM, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, tensorIso_hom, Iso.refl_hom,
    ObjectProperty.FullSubcategory.comp_hom, Functor.whiskeringRight_obj_obj,
    Functor.whiskeringRight_obj_map, Category.assoc] using hf

private theorem scalarBalance_forward [Module.Free A B] [Module.Finite A B]
    (M : Sheaf J (ModuleCat.{u + 1} A)) (N : Sheaf J (ModuleCat.{u + 1} B))
    (V : Cᵒᵖ) (m : M.obj.obj V) (b : B) (n : N.obj.obj V) :
    (scalarBalance J M N).hom.hom.app V
      (finiteScalarTensorPure J B _ N V
        (finiteScalarPure J (algebraMap A B) M V b m) n) =
      finiteScalarTensorPure J A M _ V m (b • n) := by
  let t : (M.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (algebraMap A B)).obj V := b ⊗ₜ[A] m
  have ht : (scalarRawExtensionIso J (B := B) M).inv.app V
      (finiteScalarPure J (algebraMap A B) M V b m) = t :=
    ConcreteCategory.congr_hom
      ((scalarRawExtensionIso J (B := B) M).hom_inv_id_app V) t
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (scalarBalance_fac J M N) V)
    ((finiteScalarPure J (algebraMap A B) M V b m) ⊗ₜ[B] n)
  change (scalarBalance J M N).hom.hom.app V
      (finiteScalarTensorPure J B _ N V
        (finiteScalarPure J (algebraMap A B) M V b m) n) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf J _) M
      ((Sheaf.restrictScalars J (algebraMap A B)).obj N)).app V
      ((rawBalance M.obj N.obj).hom.app V
        (((scalarRawExtensionIso J (B := B) M).inv.app V
          (finiteScalarPure J (algebraMap A B) M V b m)) ⊗ₜ[B] n)) at h
  rw [ht, rawBalance_pure] at h
  exact h

private theorem scalarBalance_inverse [Module.Free A B] [Module.Finite A B]
    (M : Sheaf J (ModuleCat.{u + 1} A)) (N : Sheaf J (ModuleCat.{u + 1} B))
    (V : Cᵒᵖ) (m : M.obj.obj V) (n : N.obj.obj V) :
    (scalarBalance J M N).inv.hom.app V (finiteScalarTensorPure J A M _ V m n) =
      finiteScalarTensorPure J B _ N V
        (finiteScalarPure J (algebraMap A B) M V 1 m) n := by
  have h := scalarBalance_forward J M N V m 1 n
  rw [one_smul] at h
  rw [← h]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (ObjectProperty.isoHom_inv_id_hom (scalarBalance J M N)) V) _

omit [EssentiallySmall.{u + 1} C] in
private theorem scalarRawExtensionIso_inv_natural [Module.Free A B] [Module.Finite A B]
    {M M' : Sheaf J (ModuleCat.{u + 1} A)} (f : M ⟶ M') :
    ((finiteScalarExtension J (algebraMap A B)).map f).hom ≫
        (scalarRawExtensionIso J (B := B) M').inv =
      (scalarRawExtensionIso J (B := B) M).inv ≫
        Functor.whiskerRight f.hom
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) := by
  have hn : Functor.whiskerRight f.hom
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) ≫
      (scalarRawExtensionIso J (B := B) M').hom =
    (scalarRawExtensionIso J (B := B) M).hom ≫
      ((finiteScalarExtension J (algebraMap A B)).map f).hom :=
    (sheafificationAdjunction J _).unit.naturality _
  apply (cancel_epi (scalarRawExtensionIso J (B := B) M).hom).1
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

private theorem tensorSheafify_inv_natural (R : Type (u + 1)) [CommRing R]
    {M M' N N' : Sheaf J (ModuleCat.{u + 1} R)} (f : M ⟶ M') (g : N ⟶ N') :
    (presheafToSheaf J (ModuleCat.{u + 1} R)).map (f.hom ⊗ₘ g.hom) ≫
        (tensorSheafify J R M' N').inv =
      (tensorSheafify J R M N).inv ≫ (f ⊗ₘ g) := by
  apply (cancel_epi (tensorSheafify J R M N).hom).1
  rw [← Category.assoc, ← tensorSheafify_natural, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem scalarBalance_natural [Module.Free A B] [Module.Finite A B]
    {M M' : Sheaf J (ModuleCat.{u + 1} A)}
    {N N' : Sheaf J (ModuleCat.{u + 1} B)} (f : M ⟶ M') (g : N ⟶ N') :
    (Sheaf.restrictScalars J (algebraMap A B)).map
        ((finiteScalarExtension J (algebraMap A B)).map f ⊗ₘ g) ≫
        (scalarBalance J M' N').hom =
      (scalarBalance J M N).hom ≫
        (f ⊗ₘ (Sheaf.restrictScalars J (algebraMap A B)).map g) := by
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} (algebraMap A B)) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  let E := finiteScalarExtension J (algebraMap A B)
  let U := Sheaf.restrictScalars J (algebraMap A B)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
  let a := presheafToSheaf J (ModuleCat.{u + 1} A)
  let b := presheafToSheaf J (ModuleCat.{u + 1} B)
  let c := (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))
    (sheafificationAdjunction J (ModuleCat.{u + 1} B))
    (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm
  let e (M : Sheaf J (ModuleCat.{u + 1} A)) (N : Sheaf J (ModuleCat.{u + 1} B)) :
      W.obj ((E.obj M).obj ⊗ N.obj) ≅ M.obj ⊗ (U.obj N).obj :=
    W.mapIso (tensorIso (scalarRawExtensionIso J (B := B) M).symm (Iso.refl N.obj)) ≪≫
      rawBalance M.obj N.obj
  have hraw : W.map ((E.map f).hom ⊗ₘ g.hom) ≫ (e M' N').hom =
      (e M N).hom ≫ (f.hom ⊗ₘ (U.map g).hom) := by
    have ht : ((E.map f).hom ⊗ₘ g.hom) ≫
        ((scalarRawExtensionIso J (B := B) M').inv ⊗ₘ 𝟙 N'.obj) =
      ((scalarRawExtensionIso J (B := B) M).inv ⊗ₘ 𝟙 N.obj) ≫
        (Functor.whiskerRight f.hom
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) ⊗ₘ g.hom) := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      rw [scalarRawExtensionIso_inv_natural]
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, tensorIso_hom,
      Iso.symm_hom, Iso.refl_hom, U, Sheaf.restrictScalars,
      sheafCompose_map_hom]
    change W.map _ ≫ (W.map _ ≫ _) = (W.map _ ≫ _) ≫ _
    have hr : W.map (Functor.whiskerRight f.hom
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap A B)) ⊗ₘ g.hom) ≫
        (rawBalance M'.obj N'.obj).hom = (rawBalance M.obj N.obj).hom ≫
          (f.hom ⊗ₘ Functor.whiskerRight g.hom
            (ModuleCat.restrictScalars.{u + 1} (algebraMap A B))) :=
      rawBalance_natural f.hom g.hom
    rw [← W.map_comp_assoc, ht, W.map_comp_assoc, hr]
    simp only [Category.assoc]
  have hq := tensorSheafify_natural J B (E.map f) g
  have hc := c.hom.naturality ((E.map f).hom ⊗ₘ g.hom)
  simp only [Functor.comp_map] at hc
  have ha := a.congr_map hraw
  simp only [Functor.map_comp] at ha
  have hi := tensorSheafify_inv_natural J A f (U.map g)
  have hb : U.map (E.map f ⊗ₘ g) ≫
      (U.map (tensorSheafify J B (E.obj M') N').hom ≫
        c.hom.app _ ≫ a.map (e M' N').hom ≫ (tensorSheafify J A M' (U.obj N')).inv) =
      (U.map (tensorSheafify J B (E.obj M) N).hom ≫ c.hom.app _ ≫
        a.map (e M N).hom ≫ (tensorSheafify J A M (U.obj N)).inv) ≫
        (f ⊗ₘ U.map g) := by
    simp only [Category.assoc]
    rw [← U.map_comp_assoc, hq, U.map_comp_assoc, reassoc_of% hc,
      reassoc_of% ha, hi]
  simpa only [scalarBalance, e, E, U, W, a, c, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, tensorIso_hom, Iso.refl_hom,
    Category.assoc] using hb

private def scalarRightBalance [Module.Free A B] [Module.Finite A B]
    (M : Sheaf J (ModuleCat.{u + 1} B)) (N : Sheaf J (ModuleCat.{u + 1} A)) :
    (Sheaf.restrictScalars J (algebraMap A B)).obj
        (M ⊗ (finiteScalarExtension J (algebraMap A B)).obj N) ≅
      (Sheaf.restrictScalars J (algebraMap A B)).obj M ⊗ N :=
  (Sheaf.restrictScalars J (algebraMap A B)).mapIso
      (β_ M ((finiteScalarExtension J (algebraMap A B)).obj N)) ≪≫
    scalarBalance J N M ≪≫
    β_ N ((Sheaf.restrictScalars J (algebraMap A B)).obj M)

private theorem scalarRightBalance_natural [Module.Free A B] [Module.Finite A B]
    {M M' : Sheaf J (ModuleCat.{u + 1} B)}
    {N N' : Sheaf J (ModuleCat.{u + 1} A)} (f : M ⟶ M') (g : N ⟶ N') :
    (Sheaf.restrictScalars J (algebraMap A B)).map
        (f ⊗ₘ (finiteScalarExtension J (algebraMap A B)).map g) ≫
        (scalarRightBalance J M' N').hom =
      (scalarRightBalance J M N).hom ≫
        ((Sheaf.restrictScalars J (algebraMap A B)).map f ⊗ₘ g) := by
  let U := Sheaf.restrictScalars J (algebraMap A B)
  change U.map _ ≫ (U.map _ ≫ _ ≫ _) = (U.map _ ≫ _ ≫ _) ≫ _
  rw [← U.map_comp_assoc, BraidedCategory.braiding_naturality, U.map_comp_assoc,
    reassoc_of% scalarBalance_natural J g f, BraidedCategory.braiding_naturality]
  simp only [Category.assoc]


private theorem scalar_kflat_of_balance
    (e : ∀ (M : Sheaf J (ModuleCat.{u + 1} B)) (N : Sheaf J (ModuleCat.{u + 1} A)),
      (Sheaf.restrictScalars J (algebraMap A B)).obj
          (M ⊗ (finiteScalarExtension J (algebraMap A B)).obj N) ≅
        (Sheaf.restrictScalars J (algebraMap A B)).obj M ⊗ N)
    (he : ∀ {M M' : Sheaf J (ModuleCat.{u + 1} B)}
        {N N' : Sheaf J (ModuleCat.{u + 1} A)} (f : M ⟶ M') (g : N ⟶ N'),
      (Sheaf.restrictScalars J (algebraMap A B)).map
          (f ⊗ₘ (finiteScalarExtension J (algebraMap A B)).map g) ≫ (e M' N').hom =
        (e M N).hom ≫ ((Sheaf.restrictScalars J (algebraMap A B)).map f ⊗ₘ g))
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((finiteScalarExtension J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hp := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have hp' (L : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) (hL : L.Acyclic) :
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic := by
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hp ((HomotopyCategory.quotient _ _).obj L)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hL)).2
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨Z, rfl⟩ := N.quotient_obj_surjective
  have hZ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hN
  let E := finiteScalarExtension J (algebraMap A B)
  let U := Sheaf.restrictScalars J (algebraMap A B)
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj Z).obj EP
  have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
  let f : (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj Z)).obj P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ e (Z.X i) (P.X j)) (by
          intro j j' hj
          change (e (Z.X i) (P.X j)).hom ≫ whiskerLeft (U.obj (Z.X i)) (P.d j j') =
            U.map (whiskerLeft (Z.X i) (E.map (P.d j j'))) ≫
              (e (Z.X i) (P.X j')).hom
          have h := (he (𝟙 (Z.X i)) (P.d j j')).symm
          change (e (Z.X i) (P.X j)).hom ≫ (U.map (𝟙 (Z.X i)) ⊗ₘ P.d j j') =
            U.map (𝟙 (Z.X i) ⊗ₘ E.map (P.d j j')) ≫ (e (Z.X i) (P.X j')).hom at h
          rw [U.map_id, id_tensorHom, id_tensorHom] at h
          exact h))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e (Z.X i) (P.X j)).hom ≫ whiskerRight (U.map (Z.d i i')) (P.X j) =
          U.map (whiskerRight (Z.d i i') (E.obj (P.X j))) ≫
            (e (Z.X i') (P.X j)).hom
        have h := (he (Z.d i i') (𝟙 (P.X j))).symm
        change (e (Z.X i) (P.X j)).hom ≫ (U.map (Z.d i i') ⊗ₘ 𝟙 (P.X j)) =
          U.map (Z.d i i' ⊗ₘ E.map (𝟙 (P.X j))) ≫ (e (Z.X i') (P.X j)).hom at h
        rw [E.map_id, tensorHom_id, tensorHom_id] at h
        exact h)
  have hUZ : ((U.mapHomologicalComplex (.up ℤ)).obj Z).Acyclic := by
    intro i
    exact (hZ i).map U
  have ht := hp' ((U.mapHomologicalComplex (.up ℤ)).obj Z) hUZ
  have hTensor : (CochainComplex.mapBifunctor Z EP (curriedTensor _)).Acyclic := by
    intro i
    let W := (CochainComplex.mapBifunctor Z EP (curriedTensor _)).sc i
    apply (W.exact_map_iff_of_faithful U).1
    exact ShortComplex.exact_of_iso
      ((HomologicalComplex.shortComplexFunctor _ _ i).mapIso
        (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)).symm) (ht i)
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hTensor
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩


/-- Exact finite-free scalar descent and the normalized ordinary balancing maps.
Source: Stacks 03CZ, 05V4, 06YY and 05RT; steps 1-6 and the ordinary part of step 7
of lem-sf-finite-free-derived-scalar-calculus.
(blueprint: lem-sf-finite-free-scalar-tensor-calculus).

Proof: sheafify the basis map and its coordinates to identify restriction after extension
with a finite direct sum. Restriction preserves the underlying abelian sheaf, hence is
exact and conservative; exactness of finite sums makes extension exact, also in rank zero.
Descend the termwise functors through quasi-isomorphisms. The localization universal
property makes this exact descent the left derived functor with its specified counit.
Localize the scalar adjunction; its localized unit and counit are exactly the two
factorization formulas in FiniteFreeScalarDescent. Homology commutes with restriction,
so the unbounded cohomology criterion reflects isomorphisms and zero objects. Localize
the basis decomposition; its inclusions are the scalar unit followed by multiplication
by the chosen basis element. Extension of K-flat complexes is K-flat by the acyclic
tensor test and tensor cancellation. For ordinary balancing use the maps
(b tensor m) tensor n to m tensor b n and m tensor n to (1 tensor m) tensor n.
Balancedness gives inverse module maps before sheafification; their sheafifications give
the displayed comparisons with exactly the stated local pure-tensor normalizations. -/
theorem finiteFreeScalarTensorCalculus :
    Nonempty (FiniteFreeScalarTensorCalculus J r basis) := by
  classical
  let : Module.Free A B := Module.Free.of_basis basis
  let : Module.Finite A B := Module.Finite.of_basis basis
  have hKflat : ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((finiteScalarExtension J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj P) :=
    scalar_kflat_of_balance J (scalarRightBalance J)
      (fun f g ↦ scalarRightBalance_natural J f g)
  exact ⟨{
    toFiniteFreeScalarDescent := scalarDescent J r basis hKflat
    sheaf_balance := scalarBalance J
    balance_forward := scalarBalance_forward J
    balance_inverse := scalarBalance_inverse J }⟩

end AlgebraicGeometry
