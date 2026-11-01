/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullbackCochainData
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData

/-! # Cochain normalization of the actual pro-etale scalar/pullback mate

Source: Stacks 07A4, 07A6 and 07A7. Transpose under the scalar adjunctions.
The ordinary restriction/pullback square and the localized scalar units give the
reverse mate equation on cochains. Invert the equation to obtain the forward
comparison; no tensor law is assumed.
(blueprint: new-sf-pro-scalar-pullback-cochain-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients
attribute [local irreducible] ProEtale.upperStar Functor.leftDerivedFunctor
  Functor.leftDerivedFunctorCounit Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh

/-- The degreewise ordinary scalar/pullback isomorphism on complexes.
Source: Stacks 07A4 (blueprint: new-sf-pro-scalar-pullback-cochain-normalization). -/
def pro_scalar_sheaf_pullback_complex_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  Functor.mapHomologicalComplexCompIso (pro_scalar_sheaf_pullback_iso φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙
        finiteVerdierOrdinaryExtension (Scheme.ProEt.topology Y) φ)) (.up ℤ)).symm

private def scalarCochainUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex
      (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ).unit (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology T) φ ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (.up ℤ)).inv.app P

private theorem scalar_rep_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ)).unit.app
        (DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
        (finiteVerdierScalarRepresentative (Scheme.ProEt.topology T) φ P) =
    DerivedCategory.Q.map (scalarCochainUnit φ T P) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.inv.app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology T) φ).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ)
  exact (ad.homEquiv _ _).apply_symm_apply _

private theorem underived_mate
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (ProEtale.upperStarRestrictScalarsIso φ f).hom)).natTrans =
        (ProEtale.lowerStarCompRestrictScalarsIso φ f).hom := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology W) φ)).injective
  change (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology W) φ)
    (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (ProEtale.upperStarRestrictScalarsIso φ f).hom))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [ProEtale.upperStarRestrictScalarsIso, TwoSquare.mk]
  erw [Equiv.apply_symm_apply]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U)))).symm

private theorem ordinary_reverse_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ((mateEquiv (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ)
      (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ)).symm
        (TwoSquare.mk _ _ _ _ (ProEtale.upperStarRestrictScalarsIso φ f).hom)).natTrans =
      (pro_scalar_sheaf_pullback_iso φ f).inv := by
  unfold pro_scalar_sheaf_pullback_iso
  exact ordinary_reverse_of_mate
    (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ)
    (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (ProEtale.upperStarRestrictScalarsIso φ f) (ProEtale.lowerStarCompRestrictScalarsIso φ f)
    (underived_mate φ f)

private theorem scalar_complex_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map
      (scalarCochainUnit φ X P) ≫
      ((Functor.mapHomologicalComplexCompIso (ProEtale.upperStarRestrictScalarsIso φ f) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (ProEtale.upperStar (ModuleCat.{u + 1} B) f ⋙
            Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (.up ℤ)).symm).hom.app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj P)) =
    scalarCochainUnit φ T
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapHomologicalComplex (.up ℤ)).map
        ((pro_scalar_sheaf_pullback_complex_iso φ f).inv.app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  change (ProEtale.upperStar (ModuleCat.{u + 1} A) f).map
      (𝟙 _ ≫ (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).unit.app (P.X i) ≫ 𝟙 _) ≫
      ((ProEtale.upperStarRestrictScalarsIso φ f).hom.app
        ((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).obj (P.X i)) ≫ 𝟙 _) =
    (𝟙 _ ≫ (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ).unit.app
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj (P.X i)) ≫ 𝟙 _) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
        (𝟙 _ ≫ (pro_scalar_sheaf_pullback_iso φ f).inv.app (P.X i))
  simp only [Category.id_comp, Category.comp_id]
  let M := P.X i
  have h := unit_mateEquiv_symm
    (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ)
    (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ)
    (TwoSquare.mk _ _ _ _ (ProEtale.upperStarRestrictScalarsIso φ f).hom) M
  change (ProEtale.upperStar (ModuleCat.{u + 1} A) f).map
      ((finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).unit.app M) ≫
      (ProEtale.upperStarRestrictScalarsIso φ f).hom.app
        ((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).obj M) =
    (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ).unit.app
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
        (((mateEquiv (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ)
          (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology T) φ)).symm
          (TwoSquare.mk _ _ _ _ (ProEtale.upperStarRestrictScalarsIso φ f).hom)).natTrans.app M)
      at h
  rw [ordinary_reverse_eq] at h
  exact h

private theorem geometric_representative_exact
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    (pro_geometric_representative A f).app P =
      Functor.exactDerivedRepresentative (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
        (Sites.proPull A f)
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) P := by
  exact Etale.representative_eq (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
    (Sites.proPull A f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac P

private theorem scalarRestrictionPullbackIso_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) :
    type_of% (Etale.exactSquareRepresentativeOfEq
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} B) f)
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
    (ProEtale.upperStarRestrictScalarsIso φ f)
    L(ProEtale.upperStar (ModuleCat.{u + 1} A) f) L(ProEtale.upperStar (ModuleCat.{u + 1} B) f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    ((pro_geometric_representative A f).app) ((pro_geometric_representative B f).app)
    (geometric_representative_exact A f) (geometric_representative_exact B f)
    (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f) rfl P) :=
  Etale.exactSquareRepresentativeOfEq
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} B) f)
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
    (ProEtale.upperStarRestrictScalarsIso φ f)
    L(ProEtale.upperStar (ModuleCat.{u + 1} A) f) L(ProEtale.upperStar (ModuleCat.{u + 1} B) f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    ((pro_geometric_representative A f).app) ((pro_geometric_representative B f).app)
    (geometric_representative_exact A f) (geometric_representative_exact B f)
    (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f) rfl P

private theorem reverse_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    (ProEtale.scalarPullbackReverseProEtale φ f).app (_root_.DerivedCategory.Q.obj P) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} B) f).map
        (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ P) ≫
      (pro_geometric_representative B f).app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj P) =
    (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).map
        ((pro_geometric_representative A f).app P) ≫
      finiteVerdierScalarRepresentative (Scheme.ProEt.topology T) φ
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((pro_scalar_sheaf_pullback_complex_iso φ f).inv.app P) := by
  let adx : ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ⊣
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ :=
    Adjunction.ofIsRightAdjoint _
  let adt' : ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ⊣
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ :=
    Adjunction.ofIsRightAdjoint _
  let ec := Functor.mapHomologicalComplexCompIso
    (ProEtale.upperStarRestrictScalarsIso φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.upperStar (ModuleCat.{u + 1} B) f ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (.up ℤ)).symm
  have hk := scalar_complex_unit φ f P
  have hef (N : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) :=
    scalarRestrictionPullbackIso_representative φ f N
  unfold ProEtale.scalarPullbackReverseProEtale
  apply Etale.normalized_scalar_mate adx adt'
    L(ProEtale.upperStar (ModuleCat.{u + 1} A) f) L(ProEtale.upperStar (ModuleCat.{u + 1} B) f)
    (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom
    (_root_.DerivedCategory.Q.obj P)
    (_root_.DerivedCategory.Q.obj
      (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj P))
    (_root_.DerivedCategory.Q.obj
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P))
    _ _ (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ P)
    (finiteVerdierScalarRepresentative (Scheme.ProEt.topology T) φ
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P))
    ((pro_geometric_representative A f).app P) _ _
    (_root_.DerivedCategory.Q.map (scalarCochainUnit φ X P) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.inv.app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj P))
    (_root_.DerivedCategory.Q.map (scalarCochainUnit φ T
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P)) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.inv.app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology T) φ).mapHomologicalComplex
          (.up ℤ)).obj
          (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P)))
    (scalar_rep_unit φ X P)
    (scalar_rep_unit φ T
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P))
  apply Etale.representative_square_unit
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ))
    L(ProEtale.upperStar (ModuleCat.{u + 1} A) f)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ)
    (scalarCochainUnit φ X P)
    (scalarCochainUnit φ T
      (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P))
    (ec.hom.app _) ((Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapHomologicalComplex
      (.up ℤ) |>.map ((pro_scalar_sheaf_pullback_complex_iso φ f).inv.app P))
    _ _ _ _ _
    ((Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.inv.app
      (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology T) φ).mapHomologicalComplex
          (.up ℤ)).obj
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P)))
    _ (_root_.DerivedCategory.Q.map ((pro_scalar_sheaf_pullback_complex_iso φ f).inv.app P))
    hk (hef _) (by
      simpa only [Sites.proPull, Functor.comp_map, Functor.comp_obj, Functor.id_obj] using
        (pro_geometric_representative A f).naturality _)
  exact (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.inv.naturality
    ((pro_scalar_sheaf_pullback_complex_iso φ f).inv.app P)

/-- The actual pro-etale scalar mate is normalized by the ordinary cochain comparison.
Source: Stacks 07A4, 07A6 and 07A7.
Proof: compute the ordinary reverse mate using iterated conjugation and the
restriction/coextension triangle. Its unit equation holds in every degree.
The exact geometric representative identifies the derived restriction square
with the localized ordinary square. Transpose that square under the derived
scalar adjunctions to compute the reverse scalar mate. Invert the resulting
normalization equation and the ordinary cochain comparison.
(blueprint: new-sf-pro-scalar-pullback-cochain-normalization). -/
theorem pro_scalar_pullback_cochain_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    (ProEtale.scalarPullbackProEtaleIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
      (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).map
        ((pro_geometric_representative A f).app P) ≫
      finiteVerdierScalarRepresentative (Scheme.ProEt.topology T) φ
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P) =
    (Sites.proPull B f).map
        (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ P) ≫
      (pro_geometric_representative B f).app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((pro_scalar_sheaf_pullback_complex_iso φ f).hom.app P) := by
  have := (ProEtale.scalarPullbackReverse_isIso φ f).1
  have h := Etale.inverse_normalization_app (ProEtale.scalarPullbackReverseProEtale φ f)
    (DerivedCategory.Q.obj P)
    ((Sites.proPull B f).map
        (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ P) ≫
      (pro_geometric_representative B f).app
        (((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj P))
    ((ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).map
        ((pro_geometric_representative A f).app P) ≫
      finiteVerdierScalarRepresentative (Scheme.ProEt.topology T) φ
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
          (.up ℤ)).obj P))
    (DerivedCategory.Q.mapIso ((pro_scalar_sheaf_pullback_complex_iso φ f).app P).symm)
    (by simpa only [Sites.proPull, Iso.app_hom, Iso.app_inv, asIso_hom,
      Functor.mapIso_hom, Iso.symm_hom, Category.assoc] using reverse_normalization φ f P)
  simpa only [ProEtale.scalarPullbackProEtaleIso, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc] using h

end WeilConjectures.FiniteFreeCoefficients
