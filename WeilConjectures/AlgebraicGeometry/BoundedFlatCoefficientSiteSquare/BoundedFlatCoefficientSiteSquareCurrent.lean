/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # The bounded flat coefficient/site square

Source: Stacks Project, Tags 06YQ, 0G7E, 06YY, 07A4, 08G1 and 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square).

The input category is the full category of flat-term complexes supported in the
specified interval. All three comparison isomorphisms below are natural on this
category. Their normalization uses the actual ordinary and derived scalar units,
restriction square and scalar-adjunction mate, with no retained coefficient witness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.BoundedFlatCoefficientSiteSquare

open CoefficientScalarRepresentatives

/-- Termwise ordinary scalar extension, retaining its target-ring action.
Source: Stacks 03EK (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
abbrev scalarComplex {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :=
  (ordinaryExtension J φ).mapHomologicalComplex (.up ℤ)

/-- Termwise exact comparison inverse image in the existing fixed-ring presentation.
Source: Stacks 03D2 (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
abbrev siteComplex (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex (.up ℤ)

/-- The full input category imposes exactly flat terms and the stated interval support.
Source: Stacks 06YQ and 08G1
(blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def inputs (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] (a b : ℤ) :
    ObjectProperty (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  fun P ↦ (∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
    ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)

/-- The ordinary scalar/site mate of the inverse restriction square. Its inverse is
exactly the usual tensor/site comparison, with the B-action on the coefficient factor.
Source: Stacks 03EL (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def ordinaryMate (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        ordinaryExtension (Scheme.ProEt.topology X) φ ⟶
      ordinaryExtension X.smallEtaleTopology φ ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X :=
  ((mateEquiv (ordinaryAdjunction X.smallEtaleTopology φ)
    (ordinaryAdjunction (Scheme.ProEt.topology X) φ)).symm
      (TwoSquare.mk _ _ _ _ (comparisonRestriction X φ).inv)).natTrans

/-- The same specified scalar/site mate on cochain complexes, including composition
identifications; no comparison isomorphism is chosen here.
Source: Stacks 03EL (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def cochainMate (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    siteComplex X A ⋙ scalarComplex (Scheme.ProEt.topology X) φ ⟶
      scalarComplex X.smallEtaleTopology φ ⋙ siteComplex X B :=
  (Functor.mapHomologicalComplexCompIso
    (F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (G := ordinaryExtension (Scheme.ProEt.topology X) φ) (Iso.refl _) (.up ℤ)).hom ≫
    NatTrans.mapHomologicalComplex (ordinaryMate X φ) (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso
      (F := ordinaryExtension X.smallEtaleTopology φ)
      (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
      (Iso.refl _) (.up ℤ)).inv

/-- The second displayed representative identification, natural even before imposing
flatness or bounds: Q(N_A P) is N_A(Q P).
Source: Stacks 06YY (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def siteLocalization (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    siteComplex X A ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryFactors.symm

private theorem boundedFlat_properties {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R]
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) (a b : ℤ)
    (hflat : ∀ q, ObjectProperty.flat (P.X q))
    (hsupport : ∀ q, q < a ∨ b < q → IsZero (P.X q)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      _root_.DerivedCategory.torAmplitudeIn _ a b (DerivedCategory.Q.obj P) := by
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P a).2
    (fun q hq ↦ hsupport q (.inl hq))
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).2
    (fun q hq ↦ hsupport q (.inr hq))
  exact ⟨CochainComplex.kFlat_of_bounded_of_flat P a b hflat,
    _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat P a b hflat⟩

section ScalarSite

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)

set_option maxHeartbeats 2000000 in
-- The scalar tensor identification uses a long sheafification instance chain.
set_option synthInstance.maxHeartbeats 400000 in
-- Sheafification and tensor instances on the small site require a larger search budget.
/-- The scalar representative arrows are natural in all maps of complexes.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
private theorem representative_naturality
    {P Q : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ} (f : P ⟶ Q) :
    (extension J a).map (DerivedCategory.Q.map f) ≫ representative J a Q =
      representative J a P ≫
        DerivedCategory.Q.map (((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).map f) := by
  unfold representative
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  apply congrArg ((adjunction J a).homEquiv _ _).symm
  change DerivedCategory.Q.map f ≫
      (DerivedCategory.Q.map (((ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv.app _) =
    (DerivedCategory.Q.map
        (((ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv.app _) ≫ _
  have hu := ((ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ)).unit.naturality f
  dsimp only [Functor.id_map] at hu
  rw [← DerivedCategory.Q.map_comp_assoc, hu,
    DerivedCategory.Q.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using
    congrArg (fun t ↦ DerivedCategory.Q.map
    (((ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ)).unit.app P) ≫ t)
      ((Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv.naturality
        (((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).map f))

attribute [local irreducible] ordinaryExtension ordinaryAdjunction

set_option synthInstance.maxHeartbeats 400000 in
-- The monoidal structure on complexes uses site sheafification instances.
/-- On a K-flat complex, the specified scalar representative is invertible.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
private theorem representative_isIso
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (representative J a P) := by
  exact Adjunction.isIso_cochainTranspose_of_kFlat
    (ordinaryExtension J a) (Sheaf.restrictScalars J a)
    (ordinaryAdjunction J a) (adjunction J a) P hP

private def representativeTransformation :
    DerivedCategory.Q ⋙ extension J a ⟶
      (ordinaryExtension J a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app := representative J a
  naturality _ _ f := representative_naturality J a f

private theorem representative_unit
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (adjunction J a).unit.app (DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars J a).map (representative J a P) ≫
      (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.hom.app
        (((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map (((ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ)).unit.app P)
      := by
  have h := ((adjunction J a).homEquiv _ _).apply_symm_apply
    (DerivedCategory.Q.map (((ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv.app
        (((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).obj P))
  change (adjunction J a).unit.app (DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars J a).map (representative J a P) = _ at h
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id]


end ScalarSite

section Comparison

variable (T : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (a : A →+* B)

-- Restricting the site commutes with the pointwise coextension adjunction.
private theorem restrict_coextend_mate (φ : A →+* B) :
    (mateEquiv
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ)
      (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ)
      (TwoSquare.mk _ _ _ _
        (show ProEtale.comparisonLowerStar (ModuleCat.{u + 1} B) T ⋙
            Sheaf.restrictScalars T.smallEtaleTopology φ ⟶
          Sheaf.restrictScalars (Scheme.ProEt.topology T) φ ⋙
            ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T from 𝟙 _))).natTrans = 𝟙 _ := by
  ext F V x
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
    Category.id_comp]
  change (((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app
      ((ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).obj
        (F.obj.obj ((Scheme.toProEt T).op.obj V)))) ≫
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).map
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).counit.app
          (F.obj.obj ((Scheme.toProEt T).op.obj V)))).hom x = x
  exact congrArg (fun f ↦ f.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components _)

private theorem comparison_restrict_mate (φ : A →+* B) :
    (mateEquiv (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T)
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
      (TwoSquare.mk _ _ _ _ (comparisonRestriction T φ).inv)).natTrans = 𝟙 _ := by
  exact mate_of_conjugate
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ)
    (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ)
    (Iso.refl _) (𝟙 _) (restrict_coextend_mate T φ)


private theorem ordinary_scalar_mate_isIso (φ : A →+* B) :
    IsIso (((mateEquiv (ordinaryAdjunction T.smallEtaleTopology φ)
      (ordinaryAdjunction (Scheme.ProEt.topology T) φ)).symm
      (TwoSquare.mk _ _ _ _ (comparisonRestriction T φ).inv)).natTrans) := by
  apply isIso_left_mate_of_iterated
    (ordinaryAdjunction T.smallEtaleTopology φ)
    (ordinaryAdjunction (Scheme.ProEt.topology T) φ)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T)
  rw [comparison_restrict_mate]
  infer_instance

private theorem cochain_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ P]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The derived scalar mate on complexes is the localized ordinary mate, under the
specified scalar representative arrows and the exact site localization factors.
Source: Stacks 03EL and 06YY
(blueprint: def-sp-coefficient-scalar-representatives).
Proof: transpose both sides through the target scalar adjunction. The defining
transpose of each representative replaces its unit composite by the localized
ordinary unit. Exact localization identifies the restriction square component
with its ordinary component. Naturality and the ordinary mate unit identity then
identify the two transposes, and injectivity of the adjunction bijection finishes. -/
private theorem comparisonMap_representative
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (comparisonMap T a).app (DerivedCategory.Q.obj P) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.map
        (representative T.smallEtaleTopology a P) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategoryFactors.hom.app
        (((ordinaryExtension T.smallEtaleTopology a).mapHomologicalComplex (.up ℤ)).obj P) =
    (extension (Scheme.ProEt.topology T) a).map
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} A) T).mapDerivedCategoryFactors.hom.app P) ≫
      representative (Scheme.ProEt.topology T) a
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (((mateEquiv (ordinaryAdjunction T.smallEtaleTopology a)
          (ordinaryAdjunction (Scheme.ProEt.topology T) a)).symm
          (TwoSquare.mk _ _ _ _ (comparisonRestriction T a).inv)).natTrans)
          (.up ℤ)).app P) := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T
  let τ := (NatTrans.mapHomologicalComplex (comparisonRestriction T a).inv (.up ℤ))
  have hτ (N : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
      F.mapDerivedCategory.map
        ((Sheaf.restrictScalars T.smallEtaleTopology a).mapDerivedCategoryFactors.hom.app N) ≫
        F.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (τ.app N) =
      (derivedComparisonRestriction T a).inv.app (DerivedCategory.Q.obj N) ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) a).map
          (G.mapDerivedCategoryFactors.hom.app N) ≫
        (Sheaf.restrictScalars
          (Scheme.ProEt.topology T) a).mapDerivedCategoryFactors.hom.app _ := by
    rw [derivedComparisonRestriction, derived_square_inv]
    exact cochain_square_normalization (comparisonRestriction T a).symm N
  have h := left_mate_normalization
    ((ordinaryAdjunction T.smallEtaleTopology a).mapHomologicalComplex (.up ℤ))
    ((ordinaryAdjunction (Scheme.ProEt.topology T) a).mapHomologicalComplex (.up ℤ))
    (adjunction T.smallEtaleTopology a) (adjunction (Scheme.ProEt.topology T) a)
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (representativeTransformation T.smallEtaleTopology a)
    (representativeTransformation (Scheme.ProEt.topology T) a)
    (Sheaf.restrictScalars T.smallEtaleTopology a).mapDerivedCategoryFactors
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) a).mapDerivedCategoryFactors
    F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors
    τ (derivedComparisonRestriction T a).inv
    (representative_unit T.smallEtaleTopology a)
    (representative_unit (Scheme.ProEt.topology T) a) hτ P
  have hm : (((mateEquiv
      (G := F.mapHomologicalComplex (.up ℤ))
      (H := G.mapHomologicalComplex (.up ℤ))
      ((ordinaryAdjunction T.smallEtaleTopology a).mapHomologicalComplex (.up ℤ))
      ((ordinaryAdjunction (Scheme.ProEt.topology T) a).mapHomologicalComplex (.up ℤ))).symm
      (TwoSquare.mk _ _ _ _ τ)).natTrans.app P) =
      (NatTrans.mapHomologicalComplex
        (((mateEquiv (ordinaryAdjunction T.smallEtaleTopology a)
          (ordinaryAdjunction (Scheme.ProEt.topology T) a)).symm
          (TwoSquare.mk _ _ _ _ (comparisonRestriction T a).inv)).natTrans)
          (.up ℤ)).app P := by
    ext q
    simp only [left_mate_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
      Adjunction.mapHomologicalComplex_unit_app_f,
      Adjunction.mapHomologicalComplex_counit_app_f]
    rfl
  simpa only [representativeTransformation, hm, F, G, comparisonMap] using h

/-- The ordinary scalar mate of the comparison restriction square is invertible.
Source: Stacks 03EL (blueprint: def-sp-coefficient-scalar-representatives). -/
private theorem ordinaryComparisonMap_isIso :
    IsIso (((mateEquiv (ordinaryAdjunction T.smallEtaleTopology a)
      (ordinaryAdjunction (Scheme.ProEt.topology T) a)).symm
      (TwoSquare.mk _ _ _ _ (comparisonRestriction T a).inv)).natTrans) := by
  exact ordinary_scalar_mate_isIso T a


end Comparison

private def scalarRepresentative {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    DerivedCategory.Q ⋙ extension J φ ⟶ scalarComplex J φ ⋙ DerivedCategory.Q where
  app := representative J φ
  naturality _ _ f := representative_naturality J φ f

private theorem cochainMate_app (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (cochainMate X φ).app P =
      (NatTrans.mapHomologicalComplex (ordinaryMate X φ) (.up ℤ)).app P := by
  simp only [cochainMate, NatTrans.comp_app,
    Functor.mapHomologicalComplexCompIso_refl_hom_app, Category.id_comp]
  have h := Functor.mapHomologicalComplexCompIso_refl_hom_app
    (F := ordinaryExtension X.smallEtaleTopology φ)
    (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X) (.up ℤ) P
  have hi := (Functor.mapHomologicalComplexCompIso
    (F := ordinaryExtension X.smallEtaleTopology φ)
    (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (Iso.refl _) (.up ℤ)).inv_hom_id_app P
  rw [h, Category.comp_id] at hi
  rw [hi, Category.comp_id]

set_option synthInstance.maxHeartbeats 400000 in
-- The comparison-site instances require a larger search budget.
/-- Bounded flat models on the coefficient/site square and their canonical normalization.
Source: Stacks 06YQ, 0G7E, 06YY, 07A4, 08G1 and 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square).

Proof, following the node:
1. Exact comparison inverse image preserves zero terms. Flat inverse image and flat
scalar extension preserve flat terms, including the target action on B, so all five
complexes have flat terms and the same support.
2. Apply bounded-above-flat K-flatness (06YQ) to each complex, testing arbitrary
acyclic complexes. The same bounded-flat tensor computation proves the universal
Tor interval (08G1); comparison Tor transport also tests all pro-etale modules.
3. The scalar representative arrows are the transposes of the localized ordinary
units. K-flat representatives make them invertible (06YY). The ordinary scalar/site
mate is the inverse B-linear tensor comparison (03EL), naturally in chain maps.
4. Exact localization gives siteLocalization. Scalar representatives and its image
under scalar extension give the other two displayed derived identifications.
5. Compute the derived mate using its unit--restriction--counit formula. On these
representatives it is the localized ordinary mate. Thus the derived image of the
inverse cochain mate is the inverse of the specified Delta. The representative
normalizations below express this equality without any arbitrary isomorphism.
No flatness of B over A, projective dimension, constructibility, or condition on X
is used. -/
theorem boundedFlat_coefficient_site_square (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (a b : ℤ) (hab : a ≤ b) :
    ∃ (χ : (inputs X A a b).ι ⋙ scalarComplex X.smallEtaleTopology φ ⋙ siteComplex X B ≅
          (inputs X A a b).ι ⋙ siteComplex X A ⋙
            scalarComplex (Scheme.ProEt.topology X) φ)
      (e : (inputs X A a b).ι ⋙ scalarComplex X.smallEtaleTopology φ ⋙ DerivedCategory.Q ≅
          (inputs X A a b).ι ⋙ DerivedCategory.Q ⋙ extension X.smallEtaleTopology φ)
      (p : (inputs X A a b).ι ⋙ siteComplex X A ⋙
            scalarComplex (Scheme.ProEt.topology X) φ ⋙ DerivedCategory.Q ≅
          (inputs X A a b).ι ⋙ DerivedCategory.Q ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
              extension (Scheme.ProEt.topology X) φ),
      ∀ P : (inputs X A a b).FullSubcategory,
        (∀ q : ℤ, ObjectProperty.flat (P.obj.X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (P.obj.X q)) ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P.obj ∧
        (∀ q : ℤ, ObjectProperty.flat
          (((scalarComplex X.smallEtaleTopology φ).obj P.obj).X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero
          (((scalarComplex X.smallEtaleTopology φ).obj P.obj).X q)) ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
          ((scalarComplex X.smallEtaleTopology φ).obj P.obj) ∧
        (∀ q : ℤ, ObjectProperty.flat (((siteComplex X A).obj P.obj).X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (((siteComplex X A).obj P.obj).X q)) ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat ((siteComplex X A).obj P.obj) ∧
        (∀ q : ℤ, ObjectProperty.flat
          (((scalarComplex (Scheme.ProEt.topology X) φ).obj
            ((siteComplex X A).obj P.obj)).X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero
          (((scalarComplex (Scheme.ProEt.topology X) φ).obj
            ((siteComplex X A).obj P.obj)).X q)) ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
          ((scalarComplex (Scheme.ProEt.topology X) φ).obj ((siteComplex X A).obj P.obj)) ∧
        (∀ q : ℤ, ObjectProperty.flat
          (((siteComplex X B).obj ((scalarComplex X.smallEtaleTopology φ).obj P.obj)).X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero
          (((siteComplex X B).obj ((scalarComplex X.smallEtaleTopology φ).obj P.obj)).X q)) ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
          ((siteComplex X B).obj ((scalarComplex X.smallEtaleTopology φ).obj P.obj)) ∧
        χ.inv.app P = (cochainMate X φ).app P.obj ∧
        e.inv.app P = representative X.smallEtaleTopology φ P.obj ∧
        p.inv.app P =
          (extension (Scheme.ProEt.topology X) φ).map ((siteLocalization X A).inv.app P.obj) ≫
            representative (Scheme.ProEt.topology X) φ ((siteComplex X A).obj P.obj) ∧
        (extension (Scheme.ProEt.topology X) φ).map ((siteLocalization X A).inv.app P.obj) ≫
            representative (Scheme.ProEt.topology X) φ ((siteComplex X A).obj P.obj) ≫
            DerivedCategory.Q.map (χ.inv.app P) ≫
            (siteLocalization X B).hom.app ((scalarComplex X.smallEtaleTopology φ).obj P.obj) =
          (comparisonMap X φ).app (DerivedCategory.Q.obj P.obj) ≫
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
              (representative X.smallEtaleTopology φ P.obj) ∧
        Etale.DerivedCategory.hasTorAmplitudeIn A X a b (DerivedCategory.Q.obj P.obj) ∧
        Etale.DerivedCategory.hasTorAmplitudeIn B X a b
          (DerivedCategory.Q.obj ((scalarComplex X.smallEtaleTopology φ).obj P.obj)) ∧
        Scheme.HasFixedCoefficientProEtaleTorAmplitude X A
          (DerivedCategory.Q.obj ((siteComplex X A).obj P.obj)) a b ∧
        Scheme.HasFixedCoefficientProEtaleTorAmplitude X B
          (DerivedCategory.Q.obj ((scalarComplex (Scheme.ProEt.topology X) φ).obj
            ((siteComplex X A).obj P.obj))) a b ∧
        Scheme.HasFixedCoefficientProEtaleTorAmplitude X B
          (DerivedCategory.Q.obj ((siteComplex X B).obj
            ((scalarComplex X.smallEtaleTopology φ).obj P.obj))) a b := by
  classical
  have hP (P : (inputs X A a b).FullSubcategory) :=
    boundedFlat_properties X.smallEtaleTopology P.obj a b P.property.1 P.property.2
  have hfE (P : (inputs X A a b).FullSubcategory) (q : ℤ) :
      ObjectProperty.flat (((scalarComplex X.smallEtaleTopology φ).obj P.obj).X q) :=
    Sheaf.flat_extendScalars_obj X.smallEtaleTopology φ (P.property.1 q)
  have hsE (P : (inputs X A a b).FullSubcategory) (q : ℤ)
      (hq : q < a ∨ b < q) :
      IsZero (((scalarComplex X.smallEtaleTopology φ).obj P.obj).X q) :=
    (ordinaryExtension X.smallEtaleTopology φ).map_isZero (P.property.2 q hq)
  have hE (P : (inputs X A a b).FullSubcategory) :=
    boundedFlat_properties X.smallEtaleTopology _ a b (hfE P) (hsE P)
  have hfN (P : (inputs X A a b).FullSubcategory) (q : ℤ) :
      ObjectProperty.flat (((siteComplex X A).obj P.obj).X q) :=
    ProEtale.flat_comparisonUpperStar_obj (P.property.1 q)
  have hsN (P : (inputs X A a b).FullSubcategory) (q : ℤ)
      (hq : q < a ∨ b < q) : IsZero (((siteComplex X A).obj P.obj).X q) :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).map_isZero (P.property.2 q hq)
  have hN (P : (inputs X A a b).FullSubcategory) :=
    boundedFlat_properties (Scheme.ProEt.topology X) _ a b (hfN P) (hsN P)
  have hfNE (P : (inputs X A a b).FullSubcategory) (q : ℤ) :
      ObjectProperty.flat (((scalarComplex (Scheme.ProEt.topology X) φ).obj
        ((siteComplex X A).obj P.obj)).X q) :=
    Sheaf.flat_extendScalars_obj (Scheme.ProEt.topology X) φ (hfN P q)
  have hsNE (P : (inputs X A a b).FullSubcategory) (q : ℤ)
      (hq : q < a ∨ b < q) : IsZero
      (((scalarComplex (Scheme.ProEt.topology X) φ).obj
        ((siteComplex X A).obj P.obj)).X q) :=
    (ordinaryExtension (Scheme.ProEt.topology X) φ).map_isZero (hsN P q hq)
  have hNE (P : (inputs X A a b).FullSubcategory) :=
    boundedFlat_properties (Scheme.ProEt.topology X) _ a b (hfNE P) (hsNE P)
  have hfEN (P : (inputs X A a b).FullSubcategory) (q : ℤ) :
      ObjectProperty.flat (((siteComplex X B).obj
        ((scalarComplex X.smallEtaleTopology φ).obj P.obj)).X q) :=
    ProEtale.flat_comparisonUpperStar_obj (hfE P q)
  have hsEN (P : (inputs X A a b).FullSubcategory) (q : ℤ)
      (hq : q < a ∨ b < q) : IsZero
      (((siteComplex X B).obj ((scalarComplex X.smallEtaleTopology φ).obj P.obj)).X q) :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map_isZero (hsE P q hq)
  have hEN (P : (inputs X A a b).FullSubcategory) :=
    boundedFlat_properties (Scheme.ProEt.topology X) _ a b (hfEN P) (hsEN P)
  have : IsIso (ordinaryMate X φ) := ordinaryComparisonMap_isIso X φ
  have : IsIso (cochainMate X φ) := by
    unfold cochainMate
    have : IsIso (NatTrans.mapHomologicalComplex (ordinaryMate X φ) (.up ℤ)) :=
      (NatIso.mapHomologicalComplex (asIso (ordinaryMate X φ)) (.up ℤ)).isIso_hom
    infer_instance
  let χ := (Functor.isoWhiskerLeft (inputs X A a b).ι (asIso (cochainMate X φ))).symm
  let re := Functor.whiskerLeft (inputs X A a b).ι
    (scalarRepresentative X.smallEtaleTopology φ)
  have : IsIso re := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro P
    exact representative_isIso X.smallEtaleTopology φ P.obj (hP P).1
  let e := (asIso re).symm
  let rp := Functor.whiskerRight
      (Functor.whiskerLeft (inputs X A a b).ι (siteLocalization X A).inv)
      (extension (Scheme.ProEt.topology X) φ) ≫
    Functor.whiskerLeft ((inputs X A a b).ι ⋙ siteComplex X A)
      (scalarRepresentative (Scheme.ProEt.topology X) φ)
  have : IsIso rp := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro P
    have := representative_isIso (Scheme.ProEt.topology X) φ
      ((siteComplex X A).obj P.obj) (hN P).1
    dsimp only [rp, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, scalarRepresentative]
    change IsIso ((extension (Scheme.ProEt.topology X) φ).map
      ((siteLocalization X A).inv.app P.obj) ≫
        representative (Scheme.ProEt.topology X) φ ((siteComplex X A).obj P.obj))
    infer_instance
  let p := (asIso rp).symm
  refine ⟨χ, e, p, fun P ↦ ⟨P.property.1, P.property.2, (hP P).1,
    hfE P, hsE P, (hE P).1, hfN P, hsN P, (hN P).1,
    hfNE P, hsNE P, (hNE P).1, hfEN P, hsEN P, (hEN P).1,
    rfl, rfl, rfl, ?_, ?_, ?_, ⟨hab, (hN P).2⟩,
    ⟨hab, (hNE P).2⟩, ⟨hab, (hEN P).2⟩⟩⟩
  · have h := comparisonMap_representative X φ P.obj
    have hc := cochainMate_app X φ P.obj
    change _ ≫ _ ≫ DerivedCategory.Q.map ((cochainMate X φ).app P.obj) ≫ _ = _
    rw [hc]
    apply (cancel_mono
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} B) X).mapDerivedCategoryFactors.hom.app
          ((scalarComplex X.smallEtaleTopology φ).obj P.obj))).1
    simpa only [Category.assoc, siteLocalization, Iso.symm_inv,
      Iso.symm_hom, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id,
      siteComplex, scalarComplex, ordinaryMate] using h.symm
  · exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 (hP P).2
  · exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 (hE P).2

end AlgebraicGeometry.BoundedFlatCoefficientSiteSquare
