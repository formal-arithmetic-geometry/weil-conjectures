/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import Sheaf.AlgebraicGeometry.CommutativeConstantSliceRestriction
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientSliceOrdinary

/-! # Derived coefficient extension under profinite slice restriction

Source: Hemo--Richarz--Scholbach, (3.1)--(3.2), Remark 3.2; Stacks 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits

private noncomputable def compareOnResolvingLocalization
    {B D E : Type*} [Category* B] [Category* D] [Category* E]
    (L : B ⥤ D) (P : ObjectProperty B)
    (W : MorphismProperty P.FullSubcategory) [(P.ι ⋙ L).IsLocalization W]
    (F G : D ⥤ E) (H : B ⥤ E)
    (α : L ⋙ F ⟶ H) (β : L ⋙ G ⟶ H)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app X)) : F ≅ G := by
  have : IsIso (Functor.whiskerLeft P.ι α) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ hα X.obj X.property
  have : IsIso (Functor.whiskerLeft P.ι β) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ hβ X.obj X.property
  exact (Localization.fullyFaithfulWhiskeringLeft (P.ι ⋙ L) W E).preimageIso
    ((Functor.associator _ _ _) ≪≫ asIso (Functor.whiskerLeft P.ι α) ≪≫
      (asIso (Functor.whiskerLeft P.ι β)).symm ≪≫ (Functor.associator _ _ _).symm)

private noncomputable def cochainCounitToHomotopy
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let j : E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  exact ((Functor.whiskeringLeft _ _ _).obj q).preimage
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom T ≫ ε ≫ j.hom)

private theorem cochainCounitToHomotopy_isIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : CochainComplex A ℤ) [IsIso (ε.app K)] :
    IsIso ((cochainCounitToHomotopy E T ε).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let j : E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  have h := congr_app (((Functor.whiskeringLeft _ _ _).obj q).map_preimage
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom T ≫ ε ≫ j.hom)) K
  change (cochainCounitToHomotopy E T ε).app (q.obj K) = _ at h
  have : IsIso (j.hom.app K) := inferInstance
  have : IsIso (T.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) := inferInstance
  have hi : IsIso ((Functor.associator q DerivedCategory.Qh T).inv.app K ≫
      T.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫ ε.app K ≫ j.hom.app K) :=
    inferInstance
  exact h.symm ▸ hi

private noncomputable def compareFromCochainCounits
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive]
    (T U : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β : DerivedCategory.Q ⋙ U ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : ObjectProperty (HomotopyCategory A (.up ℤ)))
    (W : MorphismProperty P.FullSubcategory) [(P.ι ⋙ DerivedCategory.Qh).IsLocalization W]
    (hα : ∀ K : CochainComplex A ℤ,
      P ((HomotopyCategory.quotient A (.up ℤ)).obj K) → IsIso (α.app K))
    (hβ : ∀ K : CochainComplex A ℤ,
      P ((HomotopyCategory.quotient A (.up ℤ)).obj K) → IsIso (β.app K)) : T ≅ U := by
  apply compareOnResolvingLocalization DerivedCategory.Qh P W T U
    (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cochainCounitToHomotopy E T α) (cochainCounitToHomotopy E U β)
  · intro X hX
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have := hα K hX
    exact cochainCounitToHomotopy_isIso E T α K
  · intro X hX
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have := hβ K hX
    exact cochainCounitToHomotopy_isIso E U β K

private noncomputable def postCounit
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (s : B ⥤ C) [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s] :
    DerivedCategory.Q ⋙ (T ⋙ s.mapDerivedCategory) ⟶
      (E ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε s.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ)) s.mapDerivedCategoryFactors.hom

private theorem postCounit_isIso
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (s : B ⥤ C) [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (K : CochainComplex A ℤ) [IsIso (ε.app K)] :
    IsIso ((postCounit E T ε s).app K) := by
  have : IsIso (s.mapDerivedCategory.map (ε.app K)) := inferInstance
  change IsIso (𝟙 _ ≫ s.mapDerivedCategory.map (ε.app K) ≫ 𝟙 _ ≫
    s.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K))
  infer_instance

private noncomputable def preCounit
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (r : A ⥤ B) [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (E : B ⥤ C) [E.Additive] (T : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (s : C ⥤ D) [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s] :
    DerivedCategory.Q ⋙ (r.mapDerivedCategory ⋙ T ⋙ s.mapDerivedCategory) ⟶
      (r ⋙ E ⋙ s).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight r.mapDerivedCategoryFactors.hom (T ⋙ s.mapDerivedCategory) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) (postCounit E T ε s)

private theorem preCounit_isIso
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (r : A ⥤ B) [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (E : B ⥤ C) [E.Additive] (T : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (s : C ⥤ D) [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (K : CochainComplex A ℤ)
    [IsIso (ε.app ((r.mapHomologicalComplex (.up ℤ)).obj K))] :
    IsIso ((preCounit r E T ε s).app K) := by
  have := postCounit_isIso E T ε s ((r.mapHomologicalComplex (.up ℤ)).obj K)
  change IsIso (𝟙 _ ≫ (T ⋙ s.mapDerivedCategory).map
    (r.mapDerivedCategoryFactors.hom.app K) ≫ 𝟙 _ ≫
    (postCounit E T ε s).app ((r.mapHomologicalComplex (.up ℤ)).obj K))
  infer_instance

private noncomputable def restrictedUnitIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u + 1}} (e : R ≅ B) :
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)).obj
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) := by
  let U := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let BB := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  refine (SheafOfModules.fullyFaithfulForget A).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
  · let h : (U.obj (SheafOfModules.unit BB)).val.obj V ≃ₗ[R.obj.obj V]
        (SheafOfModules.unit A).val.obj V :=
      { toFun := e.inv.hom.app V
        invFun := e.hom.hom.app V
        left_inv := fun x ↦ ConcreteCategory.congr_hom
          (congrArg (fun f : B ⟶ B ↦ f.hom.app V) e.inv_hom_id) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom
          (congrArg (fun f : R ⟶ R ↦ f.hom.app V) e.hom_inv_id) x
        map_add' := map_add _
        map_smul' := by
          intro r x
          change B.obj.obj V at x
          change e.inv.hom.app V (e.hom.hom.app V r * x) = r * e.inv.hom.app V x
          rw [map_mul]
          congr 1
          exact ConcreteCategory.congr_hom
            (congrArg (fun f : R ⟶ R ↦ f.hom.app V) e.hom_inv_id) r }
    exact h.toModuleIso
  · intro V W f
    ext x
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) x

private theorem restrictIso_kflat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u + 1}}
    (e : R ≅ B)
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := B) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          e.hom)).mapHomologicalComplex
          (.up ℤ)).obj K) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let U : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    SheafOfModules.unit _
  have hu : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) U := by
    have h : ObjectProperty.flat (show SheafOfModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) from U) :=
      ObjectProperty.prop_unit ObjectProperty.flat
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R U).symm h.tensorRight
  have hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R)
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)).obj
          (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))) :=
    (exactFunctor _ _).prop_of_iso
      ((SheafOfModules.siteSheafTensorRightIso R U) ≪≫
        (CategoryTheory.MonoidalCategory.curriedTensor _).flip.mapIso
          (restrictedUnitIso e).symm ≪≫
        (SheafOfModules.siteSheafTensorRightIso R _).symm) hu
  exact (SheafOfModules.isKFlat_restrictScalars_of_flat e.hom hflat K hK).1

attribute [local irreducible] cochainCounitToHomotopy postCounit preCounit
  InternalAbelianSheafModule.sectionModuleEquivalence
  SheafOfModules.canonicalDerivedChangeOfRingsModel

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (S : Profinite.{u})

/-- The point scalar ring on the slice uses the standard localization size.
Source: Stacks 05RU (blueprint: lem-zl-profinite-coefficient-slice-base-change). -/
instance profinitePointScalarHasDerived : HasDerivedCategory.{u + 2}
    (realizationModules ((coherentTopology Profinite.{u}).over S)
      (condensedScalarRing Λ.X)) := HasDerivedCategory.standard _

/-- The direct coefficient map from constant point scalars on the slice.
Source: HRS (3.2) (blueprint: lem-zl-profinite-coefficient-slice-base-change). -/
def profiniteDirectScalarMap :
    realizationRing ((coherentTopology Profinite.{u}).over S) (condensedScalarRing Λ.X) ⟶
      Evaluation.ringSheaf ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ.X S) :=
  (constantSheaf ((coherentTopology Profinite.{u}).over S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (profiniteScalarMap Λ.X S)) ≫
    Evaluation.scalarMap ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) Over.mkIdTerminal

/-- The universal cochain extension model for the direct coefficient map.
Source: Stacks 06YY (blueprint: lem-zl-profinite-coefficient-slice-base-change). -/
def profiniteDirectScalarModel :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (profiniteDirectScalarMap Λ S) :=
  SheafOfModules.canonicalDerivedChangeOfRingsModel (profiniteDirectScalarMap Λ S)

/-- Coefficient extension commutes with exact restriction to the profinite slice.
This compares functors on all module sheaves over the constant point-scalar sheaf,
before precomposing with constant realization of ordinary modules.

Source: HRS equations (3.1)--(3.2), Remark 3.2; Stacks Tags 06YY and 07A4.
(blueprint: lem-zl-profinite-coefficient-slice-base-change).

Proof: the canonical monoidal restriction comparison identifies the section-ring
sheaf of the restricted internal ring with the restriction of the original ring
sheaf. On the terminal slice object this is profiniteSectionRingIso. Naturality
of the constant-sheaf counit then identifies the restricted original scalar map,
after the constant-ring identification, with profiniteDirectScalarMap.
For ordinary modules, restriction commutes with sheafification: a covering sieve
on a slice object is exactly a covering sieve on its underlying object. Restrict
sectionwise balanced tensors, use these ring identifications, and sheafify to
obtain the ordinary coefficient-extension comparison, natural in every module.
Restriction is exact and preserves K-flat complexes with flat terms, by ringed
topos pullback preservation. Resolve an arbitrary unbounded complex by such a
complex. The two universal cochain counits compute the two extensions on it;
localizing the ordinary comparison gives the displayed natural isomorphism.
Roofs and common refinements give independence of the resolution and naturality
on the entire derived category. Transporting sectionwise modules to internal
modules uses the given sectionModuleEquivalence, so it gives exactly mapMod of
the actual overPullback, not an auxiliary inverse image. All constructions use
covering sieves and balanced relations and apply to the empty slice as well. -/
theorem profinite_coefficient_slice_base_change :
    let e := InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ.X
    let eS := InternalAbelianSheafModule.sectionModuleEquivalence
      ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S)
    letI := Functor.additive_of_preserves_binary_products e.inverse
    letI := Functor.additive_of_preserves_binary_products eS.inverse
    let f := ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).mapMod Λ.X
    letI := Functor.additive_of_preserves_binary_products f
    Nonempty ((condensedScalarExtensionModel Λ.X).T ⋙
        e.inverse.mapDerivedCategory ⋙ f.mapDerivedCategory ≅
      (commutativeConstantSliceRestriction (coherentTopology Profinite.{u})
        (condensedScalarRing Λ.X) S).mapDerivedCategory ⋙
          (profiniteDirectScalarModel Λ S).T ⋙ eS.inverse.mapDerivedCategory) := by
  let J := coherentTopology Profinite.{u}
  let R := realizationRing J (condensedScalarRing Λ.X)
  let e := InternalAbelianSheafModule.sectionModuleEquivalence J Λ.X
  let eS := InternalAbelianSheafModule.sectionModuleEquivalence (J.over S)
    (profiniteCoefficient Λ.X S)
  let f := (J.overPullback Ab.{u + 1} S).mapMod Λ.X
  let := Functor.additive_of_preserves_binary_products e.inverse
  let := Functor.additive_of_preserves_binary_products eS.inverse
  let := Functor.additive_of_preserves_binary_products f
  let r := commutativeConstantSliceRestriction J (condensedScalarRing Λ.X) S
  let t := e.inverse ⋙ f
  let M := condensedScalarExtensionModel Λ.X
  let MS := profiniteDirectScalarModel Λ S
  obtain ⟨τ⟩ := profinite_coefficient_slice_ordinary Λ S (profiniteDirectScalarMap Λ S)
    rfl M MS
  have hk (K : CochainComplex (realizationModules J (condensedScalarRing Λ.X)) ℤ)
      (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
      CochainComplex.IsKFlatIndependentCoefficients
        (R := realizationRing (J.over S) (condensedScalarRing Λ.X))
        ((r.mapHomologicalComplex (.up ℤ)).obj K) := by
    have h := (SheafOfModules.ringedSite_restriction_exact_kflat.{u + 1, u, u + 1}
      J R S).2.2 K hK
    let i := constantSheafOverIso J CommRingCat.{u + 1} S
      (CommRingCat.of (condensedScalarRing Λ.X))
    have hi := restrictIso_kflat i _ h
    exact hi
  let εα := postCounit M.E M.T M.ε t
  let εβ := preCounit r MS.E MS.T MS.ε eS.inverse ≫
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex τ.symm (.up ℤ))
      DerivedCategory.Q).hom
  obtain ⟨P, hP⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u + 1, u, u + 1,
      u + 2, 0, 0} J R
  let W := (HomotopyCategory.quasiIso (realizationModules J (condensedScalarRing Λ.X))
    (.up ℤ)).inverseImage P.ι
  obtain ⟨V, hV, ⟨iV⟩⟩ := hP.2.1
  let := hV
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization W :=
    Functor.IsLocalization.of_iso W iV
  refine ⟨(Functor.isoWhiskerLeft M.T
      (Functor.mapDerivedCategoryCompIso e.inverse f)).symm ≪≫
    compareFromCochainCounits (M.E ⋙ t) _ _ εα εβ P W ?_ ?_⟩
  · intro K hK
    have := M.computes K (((hP.1 _).1 hK).1)
    exact postCounit_isIso M.E M.T M.ε t K
  · intro K hK
    have := MS.computes ((r.mapHomologicalComplex (.up ℤ)).obj K)
      (hk K (((hP.1 _).1 hK).1))
    have := preCounit_isIso r MS.E MS.T MS.ε eS.inverse K
    change IsIso ((preCounit r MS.E MS.T MS.ε eS.inverse).app K ≫ _)
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
