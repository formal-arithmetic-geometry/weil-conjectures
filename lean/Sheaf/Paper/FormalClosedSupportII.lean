/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q48 and M2
-/
module

public import Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.FormalClosedSupport

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import all Sheaf.Paper.CondensedFiniteFreeTensorExact
import all Sheaf.Paper.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian

/-!
# Closed support, truncation and sequential derived limits

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-lem-formal-closed-support-ii`, and Stacks Tags 09AA and 08TC
(blueprint: sk-lem-formal-closed-support-ii).

The assertion predicate records left t-exactness and the image of every Roos triangle,
using an isomorphism normalized by the product projections. It makes no choice of cones.
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 4096
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u vA vB uA uB wA wB


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two conclusions of the closed-support lemma for one of its three functors.
The product isomorphism is the canonical comparison, specified by all projections;
the boundary uses its inverse and the functor's shift comparison.
Source: blueprint sk-lem-formal-closed-support-ii, final Roos-triangle convention;
Stacks Tag 08TC (blueprint: sk-lem-formal-closed-support-ii). -/
def ClosedSupportIIAssertions
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] : Prop :=
  (∀ K : DerivedCategory A, DerivedCategory.TStructure.t.ge 0 K →
    DerivedCategory.TStructure.t.ge 0 (F.obj K)) ∧
  (∀ (K : ℕ → DerivedCategory A) [HasProduct K]
      [HasProduct (fun n ↦ F.obj (K n))],
    ∃ e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n ↦ F.obj (K n)),
      (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) ∧
      ∀ (t : ∀ n : ℕ, K (n + 1) ⟶ K n)
        (H : DerivedCategory A) (p : H ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ H⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle t H p δ →
          IsDerivedLimitTriangle (fun n ↦ F.map (t n)) (F.obj H)
            (F.map p ≫ e.hom)
            (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app H))

/-- The canonical tensor shift comparison, specialized to the recorded derived-tensor wrapper.
Source: blueprint sk-lem-formal-closed-support-ii, derived tensor clause
(blueprint: sk-lem-formal-closed-support-ii). This reuses the existing comparison induced
from K-flat representatives; it does not choose a new shift structure. -/
instance formalClosedSupportIITensor_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (K : DerivedCategory (FormalSupportModules Λ S)) :
    ((derivedTensor Λ S).obj K).CommShift ℤ :=
  DerivedCategory.commShiftTensorLeft (FormalSupportModules Λ S) K

/-- Computing a total right derived functor on a bounded-below injective resolution
shows that it preserves the nonnegative aisle. Source: Stacks Tags 013K and 070J;
blueprint sk-lem-formal-closed-support-ii, proof Step 2.
(blueprint: sk-lem-formal-closed-support-ii). -/
private theorem rightDerived_preserves_ge
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [EnoughInjectives A] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : DerivedCategory A)
    (hK : DerivedCategory.TStructure.t.ge 0 K) :
    DerivedCategory.TStructure.t.ge 0 (F.rightDerivedFunctor.obj K) := by
  obtain ⟨P, e, hP⟩ := hK
  obtain ⟨I, α, hI, hinj, _, hα⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow A 0 P
      (fun n hn ↦ P.isZero_of_isStrictlyGE 0 n hn)
  have : I.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff I 0).2 hI
  have (n : ℤ) : Injective (I.X n) := hinj n
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  let FI := (F.mapHomologicalComplex (.up ℤ)).obj I
  let e' : F.rightDerivedFunctor.obj K ≅ DerivedCategory.Q.obj FI :=
    F.rightDerivedFunctor.mapIso (e ≪≫ asIso (DerivedCategory.Q.map α) ≪≫
      (DerivedCategory.quotientCompQhIso A).symm.app I) ≪≫
      (asIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj I))).symm ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app I) ≪≫
      (DerivedCategory.quotientCompQhIso B).app FI
  exact ⟨FI, e', inferInstance⟩

/-- A triangulated additive functor transports the Roos triangle along any product
comparison satisfying the projection equations. The equation for `1 - shift` follows
by composing with every projection. Source: Stacks Tag 08TC, the Roos-triangle
argument in blueprint sk-lem-formal-closed-support-ii.
(blueprint: sk-lem-formal-closed-support-ii). -/
private theorem map_roosTriangle
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ]
    [F.Additive] [F.IsTriangulated]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    [HasProduct (fun n ↦ F.obj (K n))]
    (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n ↦ F.obj (K n)))
    (he : ∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n))
    (t : ∀ n : ℕ, K (n + 1) ⟶ K n)
    (H : DerivedCategory A) (p : H ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ H⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle t H p δ) :
    IsDerivedLimitTriangle (fun n ↦ F.map (t n)) (F.obj H)
      (F.map p ≫ e.hom)
      (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app H) := by
  have hc : F.map (towerTransitionEndomorphism t) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ F.map (t n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, Functor.map_sub,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id,
      towerProductShift, Pi.lift_π]
    rw [← Category.assoc, he]
    simp only [← F.map_comp, Pi.lift_π, Category.id_comp]
  apply Pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ h)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · change (F.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map p
    simp
  · change towerTransitionEndomorphism (fun n ↦ F.map (t n)) ≫ e.inv =
      e.inv ≫ F.map (towerTransitionEndomorphism t)
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, ← hc]
    simp
  · change (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app H) ≫
      (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
        e.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app H)
    simp

/-- Left t-exactness and countable-product preservation imply the normalized
closed-support assertions, by transporting every Roos triangle. Source: Stacks Tag 08TC;
blueprint sk-lem-formal-closed-support-ii, proof Step 8.
(blueprint: sk-lem-formal-closed-support-ii). -/
private theorem closedSupportIIAssertions_of_products
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ]
    [F.Additive] [F.IsTriangulated] [PreservesLimitsOfShape (Discrete ℕ) F]
    (hge : ∀ K : DerivedCategory A, DerivedCategory.TStructure.t.ge 0 K →
      DerivedCategory.TStructure.t.ge 0 (F.obj K)) :
    ClosedSupportIIAssertions F := by
  refine ⟨hge, ?_⟩
  intro K _ _
  let e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n ↦ F.obj (K n)) := asIso (piComparison F K)
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = F.map (Pi.π K n) :=
    piComparison_comp_π F K n
  exact ⟨e, he, fun t H p δ h ↦ map_roosTriangle F K e he t H p δ h⟩

/-- The derived-tensor comparison clause of the closed-support theorem.
The comparison is obtained from the tensor counit on the K-flat single complex L[0].
Source: blueprint sk-lem-formal-closed-support-ii.
(blueprint: sk-lem-formal-closed-support-ii)
-/
private theorem formalClosedSupportIITensorComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Z V S : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (a : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion a]
    (_hij : Set.range i = (Set.range j)ᶜ)
    (L : FormalSupportModules Λ S)
    (_hL : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ S))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ S)).obj L)) :
    Exists fun [_h : PreservesFiniteLimits (MonoidalCategory.tensorLeft L)] ↦
      Nonempty (((derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) ≅
          (MonoidalCategory.tensorLeft L).mapDerivedCategory) := by
  have h0 := ProEtale.condensed_locally_free_tensor_preservesFiniteLimits
    (condensedRingObj Λ S) L _hL
  have hr : PreservesFiniteLimits (tensorRight L) :=
    preservesFiniteLimits_of_natIso (Mod.relativeTensorRightIso L)
  have hL : PreservesFiniteLimits (tensorLeft L) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm
  refine ⟨hL, ?_⟩
  let C := FormalSupportModules Λ S
  let q := HomotopyCategory.quotient C (.up ℤ)
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj L
  have hf : ObjectProperty.flat L :=
    ⟨⟨hL, inferInstanceAs (PreservesFiniteColimits (tensorLeft L))⟩,
      ⟨hr, inferInstanceAs (PreservesFiniteColimits (tensorRight L))⟩⟩
  have hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (q.obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff P).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hf)
  have : IsIso (DerivedCategory.tensorLeftCounit (q.obj P)) :=
    DerivedCategory.isIso_tensorLeftCounit (q.obj P) hP
  let e : (DerivedCategory.singleFunctor C 0).obj L ≅
      DerivedCategory.Qh.obj (q.obj P) :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app P
  let d : q ⋙ tensorLeft (q.obj P) ≅ tensorLeft P ⋙ q :=
    Functor.Monoidal.commTensorLeft q P
  let c : DerivedCategory.Q ⋙
      tensorLeft ((DerivedCategory.singleFunctor C 0).obj L) ≅
        DerivedCategory.Q ⋙ (tensorLeft L).mapDerivedCategory :=
    Functor.isoWhiskerLeft DerivedCategory.Q ((curriedTensor _).mapIso e) ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft q (asIso (DerivedCategory.tensorLeftCounit (q.obj P))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight d DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tensorLeft P) (DerivedCategory.quotientCompQhIso C) ≪≫
      Functor.isoWhiskerRight
        (CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L)
        DerivedCategory.Q ≪≫
      (tensorLeft L).mapDerivedCategoryFactors.symm
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) _).preimageIso c⟩

open CategoryTheory.InternalAbelianSheafModule

private theorem formalSupportProductsExact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (FormalSupportModules Λ X) := by
  let E := sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)
  have h : HasExactLimitsOfShape (Discrete ℕ)
      (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)))) :=
    Scheme.ProEt.products_exact.{u, u, 0} X
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (condensedRingObj Λ X))) ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) E.symm

private theorem exactDerived_preservesProducts
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [HasLimitsOfShape (Discrete ℕ) A] [HasLimitsOfShape (Discrete ℕ) B]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  classical
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  have h (K : ℕ → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let I := fun n ↦ DerivedCategory.Q.objPreimage (K n)
    let e : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ DerivedCategory.Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor I ⋙ DerivedCategory.Q)
        F.mapDerivedCategory :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves DerivedCategory.Q (limit.isLimit (Discrete.functor I)))
        (isLimitOfPreserves (DerivedCategory.Q ⋙ F.mapDerivedCategory)
          (limit.isLimit (Discrete.functor I)))
    exact preservesLimit_of_iso_diagram F.mapDerivedCategory e
  exact preservesLimitsOfShape_of_discrete _

private theorem rightDerived_preservesProducts
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [HasLimitsOfShape (Discrete ℕ) A] [HasLimitsOfShape (Discrete ℕ) B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : ℕ → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : ℕ) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := limit.cone (Discrete.functor I)
    have : P.pt.IsKInjective :=
      CochainComplex.isKInjective_of_isLimitFan (limit.isLimit (Discrete.functor I))
    have hPL : IsLimit (DerivedCategory.Q.mapCone P) :=
      (Fan.isLimitMapConeEquiv DerivedCategory.Q I P).symm
        (DerivedCategory.isLimitFanMkQObjOfIsKInjective
          (limit.isLimit (Discrete.functor I)))
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (limit.isLimit (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun n ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c)
      (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _

private theorem mapMod_preservesProducts
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    [PreservesLimitsOfShape (Discrete ℕ) (ProEtale.upperStar Ab.{u + 1} f)] :
    PreservesLimitsOfShape (Discrete ℕ) ((ProEtale.upperStar Ab.{u + 1} f).mapMod R) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let V : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (G.obj R) ⥤
      Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} := Mod.forget (G.obj R)
  have : PreservesLimitsOfShape (Discrete ℕ) (G.mapMod R ⋙ V) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (Mod.forget R ⋙ G))
  have : ReflectsLimitsOfShape (Discrete ℕ) V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (G.mapMod R) V

private theorem immersion_supportPullback_preservesProducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsImmersion f] :
    PreservesLimitsOfShape (Discrete ℕ) (formalSupportPullback Λ f) := by
  have := (Scheme.proEtale_immersion_inverseImage_preservesLimits f).2.1
  have := preservesSmallestLimits_of_preservesLimits
    (Scheme.proEtaleSheafInverseImage f Ab.{u + 1})
  have : PreservesLimitsOfShape (Discrete ℕ) (ProEtale.upperStar Ab.{u + 1} f) :=
    preservesLimitsOfShape_of_natIso
      ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).leftAdjointUniq
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f))
  have := mapMod_preservesProducts f (condensedRingObj Λ X)
  exact inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
    (_ ⋙ (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse))

private theorem supportKernel_preservesProducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] :
    PreservesLimitsOfShape (Discrete ℕ) (formalSupportKernel Λ j) := by
  have := immersion_supportPullback_preservesProducts Λ j
  let η := (formalSupportPullbackAdjunction Λ j).unit
  let T := formalSupportPullback Λ j ⋙ lowerStar Λ j
  have : PreservesLimitsOfShape (Discrete ℕ) T := inferInstance
  have h (K : ℕ → FormalSupportModules Λ X) :
      PreservesLimit (Discrete.functor K) (formalSupportKernel Λ j) := by
    apply preservesLimit_of_preserves_limit_cone (productIsProduct K)
    let c := (formalSupportKernel Λ j).mapCone (limit.cone (Discrete.functor K))
    let f (s : Cone (Discrete.functor K ⋙ formalSupportKernel Λ j)) :
        s.pt ⟶ ∏ᶜ K :=
      Pi.lift (fun n ↦ s.π.app ⟨n⟩ ≫ kernel.ι (η.app (K n)))
    have hf (s : Cone (Discrete.functor K ⋙ formalSupportKernel Λ j)) :
        f s ≫ η.app (∏ᶜ K) = 0 := by
      apply (isLimitOfPreserves T (productIsProduct K)).hom_ext
      intro n
      change (f s ≫ η.app (∏ᶜ K)) ≫ T.map (Pi.π K n.as) = _
      rw [Category.assoc, ← η.naturality]
      simp [f, Category.assoc]
    refine { lift := fun s ↦ kernel.lift _ (f s) (hf s), fac := ?_, uniq := ?_ }
    · intro s n
      apply (cancel_mono (kernel.ι (η.app (K n.as)))).1
      simp [formalSupportKernel, f, Category.assoc, kernel.map, η]
    · intro s m hm
      apply (cancel_mono (kernel.ι (η.app (∏ᶜ K)))).1
      apply Pi.hom_ext
      intro n
      have hn := congrArg (fun z ↦ z ≫ kernel.ι (η.app (K n))) (hm ⟨n⟩)
      simpa [formalSupportKernel, f, Category.assoc, kernel.map, η] using hn
  exact preservesLimitsOfShape_of_discrete _

private theorem finiteFreeTensor_preservesProducts
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ Mod.regular R) :
    PreservesLimitsOfShape (Discrete ℕ) (Mod.tensorLeft M) := by
  let H := Functor.const (Discrete (Fin n)) ⋙
    (lim : (Discrete (Fin n) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤ _)
  let L := Functor.const (Discrete (Fin n)) ⋙
    (colim : (Discrete (Fin n) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤ _)
  let d : Mod.ihom M ≅ H :=
    (Mod.ihomMapIso e).symm ≪≫ Mod.ihomFreePowerIso n
  let adj : L ⊣ H := (constLimAdj).comp (colimConstAdj)
  let t : Mod.tensorLeft M ≅ L :=
    (Mod.ihomAdjunction M).leftAdjointUniq (adj.ofNatIsoRight d.symm)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (colim : (Discrete (Fin n) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤ _) :=
    preservesLimitsOfShape_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  have : PreservesLimitsOfShape (Discrete ℕ) L := inferInstance
  exact preservesLimitsOfShape_of_natIso t.symm

private theorem locallyFreeTensor_preservesProducts
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hL : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).obj L)) :
    PreservesLimitsOfShape (Discrete ℕ) (tensorLeft L) := by
  obtain ⟨C, hC⟩ := hL
  have (s : C.I₀) : WeaklyEtale (C.f s) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
  have h : PreservesLimitsOfShape (Discrete ℕ) (Mod.tensorLeft L) := by
    refine ⟨fun {D} ↦ ?_⟩
    have h : IsIso (limit.lift _ ((Mod.tensorLeft L).mapCone (limit.cone D))) := by
      apply ProEtale.isIso_mapMod_of_cover C R
      intro s
      have : PreservesLimitsOfShape (Discrete ℕ)
          (ProEtale.localizationRestriction Ab.{u + 1} (C.f s) inferInstance) :=
        inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
          (Functor.sheafPushforwardContinuous
            (MorphismProperty.Over.map ⊤ (show WeaklyEtale (C.f s) from inferInstance))
            Ab.{u + 1} _ _))
      have : PreservesLimitsOfShape (Discrete ℕ)
          (ProEtale.upperStar Ab.{u + 1} (C.f s)) :=
        preservesLimitsOfShape_of_natIso
          (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (C.f s) inferInstance).symm
      let F := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R
      have : PreservesLimitsOfShape (Discrete ℕ) F := mapMod_preservesProducts _ _
      obtain ⟨n, ⟨e⟩⟩ := hC s
      have : PreservesLimitsOfShape (Discrete ℕ) (Mod.tensorLeft (F.obj L)) :=
        finiteFreeTensor_preservesProducts _ e
      have : PreservesLimit D (Mod.tensorLeft L ⋙ F) :=
        preservesLimit_of_natIso D (ProEtale.pullTensorIso (C.f s) R L).symm
      exact isIso_map_lift_of_preserves D (Mod.tensorLeft L) F
    obtain ⟨hc⟩ := (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.2 h
    exact preservesLimit_of_preserves_limit_cone (limit.isLimit D) hc
  have hr : PreservesLimitsOfShape (Discrete ℕ) (tensorRight L) :=
    preservesLimitsOfShape_of_natIso (Mod.relativeTensorRightIso L)
  exact preservesLimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm

/-- Countable-product preservation for closed support, its open restriction, and
finite locally free tensor. This isolates only the product calculation: left t-exactness,
the derived-tensor comparison, and transport of Roos triangles are proved separately.

Source: blueprint main-20261015, sk-lem-formal-closed-support-ii, proof Steps 1, 3,
4, 6 and 7; Stacks Tags 09AA and 0BK6.
(blueprint: sk-lem-formal-closed-support-ii).

Proof:
1. Immersion inverse images commute with products by Tag 09AA and open slice
restriction. Direct image is a right adjoint. The kernel of the open unit commutes
with products by the kernel universal property. Thus the underived support functor
commutes with countable products.
2. Resolve every entry of a countable family by a K-injective complex. Their product
is K-injective by Tag 0BK6. Applying the support functor to that product and using
Step 1 gives the same complex as the product of the images. The derived product
comparison is therefore an isomorphism. Exact open restriction commutes with
termwise products, giving the second clause.
3. On the pro-etale cover trivializing L, tensor is a finite direct sum, including
rank zero. Its product comparison is the finite coordinate-reindexing isomorphism.
Restriction commutes with products and tensor; the local inverses glue to the inverse
of the global comparison. Exact tensor is its own derived functor, as proved by
formalClosedSupportIITensorComparison, and products are represented termwise.
This gives the third clause. These comparisons use the actual product projections,
so they prove preservation of products independently of any chosen representatives.
-/
private theorem formalClosedSupportIICore
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Z V S : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (a : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion a]
    (_hij : Set.range i = (Set.range j)ᶜ)
    (L : FormalSupportModules Λ S)
    (_hL : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ S))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ S)).obj L)) :
    PreservesLimitsOfShape (Discrete ℕ) (formalClosedSupport Λ i j).rightDerivedFunctor ∧
    PreservesLimitsOfShape (Discrete ℕ)
      ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
        (upperStar Λ a).mapDerivedCategory) ∧
    PreservesLimitsOfShape (Discrete ℕ) ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) := by
  have hX := formalSupportProductsExact Λ X
  have hZ := formalSupportProductsExact Λ Z
  have hS := formalSupportProductsExact Λ S
  have hk := supportKernel_preservesProducts Λ j
  have hi := immersion_supportPullback_preservesProducts Λ i
  have hG : PreservesLimitsOfShape (Discrete ℕ) (formalClosedSupport Λ i j) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (formalSupportKernel Λ j ⋙ formalSupportPullback Λ i))
  have hR := rightDerived_preservesProducts (formalClosedSupport Λ i j)
  have ha := immersion_supportPullback_preservesProducts Λ a
  let e : upperStar Λ a ≅ formalSupportPullback Λ a :=
    (upperStarLowerStarAdjunction Λ a).leftAdjointUniq
      (formalSupportPullbackAdjunction Λ a)
  have ha' : PreservesLimitsOfShape (Discrete ℕ) (upperStar Λ a) :=
    preservesLimitsOfShape_of_natIso e.symm
  have hDa := exactDerived_preservesProducts (upperStar Λ a)
  have hT := locallyFreeTensor_preservesProducts (condensedRingObj Λ S) L _hL
  obtain ⟨hfinite, ⟨d⟩⟩ :=
    formalClosedSupportIITensorComparison Λ ℓ _hΛ i j a _hij L _hL
  have hDT := exactDerived_preservesProducts (tensorLeft L)
  exact ⟨hR, inferInstance, preservesLimitsOfShape_of_natIso d.symm⟩

/-- The closed support functor, its open restriction, and finite locally free tensor
are left t-exact and take Roos triangles to Roos triangles for the image tower.
The coefficient disjunction uses finite-subextension-valued sections for Qbar.
The last comparison identifies derived tensor with ordinary termwise tensor.

Source: blueprint main-20261015, sk-lem-formal-closed-support-ii, all clauses;
Stacks Tags 09AA, 013K, 070J, 079P, 0BK6, 07KC and 08TC
(blueprint: sk-lem-formal-closed-support-ii).

Proof plan:
1. Cartesian coefficients identify module pullback with exact inverse image.
   The immersion limit-preservation theorem gives countable products for i*, j*, u*.
   The module adjunction makes j_* preserve limits. Kernels commute with products
   and finite limits, so G = i* ker(id -> j_*j*) is additive and left exact.
2. Module categories are Grothendieck abelian. Degreewise-injective K-injective
   resolutions give enough injectives. Resolve a nonnegative representative by a
   bounded-below injective complex; it is K-injective (Tags 013K and 070J).
   Applying G retains the lower bound, proving left t-exactness of RG.
3. Products of K-injectives are K-injective (Tag 0BK6). Compute RG on their product;
   the underived product comparison identifies it with the product of G(I_n).
   Derived products on the closed site are represented termwise (det-pe-products-derived).
4. Open restriction is exact and preserves products. Its termwise derived functor
   commutes with cohomology, so the same conclusions hold after u*.
5. Finite locally free tensor preserves finite limits by the condensed finite-free
   tensor theorem, and colimits by tensor-Hom adjunction. Thus it is exact and its
   termwise functor commutes with cohomology. L[0] is K-flat. The derived-tensor
   descent theorem identifies L[0] tensor^L - naturally with termwise tensor.
6. On a trivializing pro-etale cover, the tensor/product comparison is the finite
   coordinate-reindexing isomorphism, including rank zero. Restriction commutes with
   products and tensor (localized-site tensor restriction); the local inverses glue.
7. Termwise derived products and step 6 give countable-product preservation for tensor.
   Additive right derivation and exact termwise descent give triangulated functors.
8. For a tower with shift s, normalize the product comparison phi by projections.
   The product universal property gives phi F(s) = s' phi, hence the same identity
   for 1-s. Apply F to the Roos triangle and transport its product vertices by phi.
   This is precisely the image tower's Roos triangle. No canonical comparison
   between arbitrary cones is asserted.
-/
theorem formalClosedSupportII
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Z V S : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (a : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion a]
    (_hij : Set.range i = (Set.range j)ᶜ)
    (L : FormalSupportModules Λ S)
    (_hL : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ S))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ S)).obj L)) :
    ClosedSupportIIAssertions (formalClosedSupport Λ i j).rightDerivedFunctor ∧
    ClosedSupportIIAssertions ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
      (upperStar Λ a).mapDerivedCategory) ∧
    ClosedSupportIIAssertions ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) ∧
    Exists fun [_h : PreservesFiniteLimits (MonoidalCategory.tensorLeft L)] ↦
      Nonempty (((derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) ≅
          (MonoidalCategory.tensorLeft L).mapDerivedCategory) := by
  obtain ⟨hP, hPa, hPL⟩ := formalClosedSupportIICore Λ ℓ _hΛ i j a _hij L _hL
  obtain ⟨hfinite, ⟨e⟩⟩ :=
    formalClosedSupportIITensorComparison Λ ℓ _hΛ i j a _hij L _hL
  refine ⟨closedSupportIIAssertions_of_products _ (fun K hK ↦
    rightDerived_preserves_ge _ K hK), ?_, ?_, hfinite, ⟨e⟩⟩
  · apply closedSupportIIAssertions_of_products
    intro K hK
    have : ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K).IsGE 0 :=
      ⟨rightDerived_preserves_ge _ K hK⟩
    exact ((upperStar Λ a).isGE_mapDerivedCategory_obj _ 0).ge
  · have : ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)).IsTriangulated :=
      DerivedCategory.isTriangulated_tensorLeft _ _
    apply closedSupportIIAssertions_of_products
    intro K hK
    have : K.IsGE 0 := ⟨hK⟩
    have ht := (tensorLeft L).isGE_mapDerivedCategory_obj K 0
    exact (DerivedCategory.TStructure.t.ge 0).prop_of_iso (e.app K).symm ht.ge

end AlgebraicGeometry.ProEtale.CondensedRing
