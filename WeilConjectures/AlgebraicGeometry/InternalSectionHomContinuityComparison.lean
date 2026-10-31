/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalSectionScalarHomTransportData
public import WeilConjectures.AlgebraicGeometry.InternalSectionHomComparisonData
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.InternalSectionDerivedTensorComparison
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomFilteredColimitData
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.AlgebraicGeometry.InternalSectionTotalComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.RingObjectSheaf
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Continuity and scalar evaluation under section reconstruction

Source: Stacks Project, Tags 08J9, 0A95, 03EK, 07A4 and 07A6; the agent
presentation-transport argument in the DAG
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).

The continuity arrows below are termwise colimit arrows of whole functorial
representative systems. They are not colimits formed in a derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- These max-universe instances leave an unused coefficient universe unresolved here.
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

attribute [local irreducible]
  CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence
  CategoryTheory.Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local instance] isCommMonObj_condensedRingObj coefficientToMonComm

private instance nativeComm
    (R : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (Y : Scheme.{u}) :
    IsCommMonObj (condensedRingObj.{u} R Y) :=
  isCommMonObj_condensedRingObj R Y

private instance comparisonAdditive
    (R : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (Y : Scheme.{u}) :
    (equivalence.{u} R Y).functor.Additive :=
  comparison_additive (Scheme.ProEt.topology Y) (condensedRingObj.{u} R Y)


attribute [local irreducible] CondensedRing.derivedTensor CondensedRing.derivedHom
  CondensedRing.derivedTensorHomAdjunction₂
    internalScalarAdjunction
  internalRestrictionComp internalRestrictionId sectionExtensionComp sectionExtensionId
  CategoryTheory.Mod.derivedMonoidalCategory
  CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIso

attribute [local irreducible] internalHomRepresentative homRepresentativeIso

universe a₀ b₀ a₁ b₁ i



universe a b c d
private theorem adjoint_identity_transport
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {F U : C ⥤ C} {L V : D ⥤ D} (ad : F ⊣ U) (bd : L ⊣ V)
    (E : C ⥤ D) (r : U ⋙ E ≅ E ⋙ V) (t : F ⋙ E ≅ E ⋙ L)
    (hn : ∀ K N (f : F.obj K ⟶ N),
      E.map (ad.homEquiv K N f) ≫ r.hom.app N =
        bd.homEquiv _ _ (t.inv.app K ≫ E.map f))
    (i : U ≅ 𝟭 C) (j : V ≅ 𝟭 D)
    (hr : ∀ N, E.map (i.hom.app N) = r.hom.app N ≫ j.hom.app (E.obj N))
    (K : C) :
    E.map (((ad.ofNatIsoRight i).leftAdjointUniq Adjunction.id).hom.app K) =
      t.hom.app K ≫
        ((bd.ofNatIsoRight j).leftAdjointUniq Adjunction.id).hom.app (E.obj K) := by
  apply (cancel_epi (t.inv.app K)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply ((bd.ofNatIsoRight j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, ← hn, Category.assoc, ← hr,
    ← E.map_comp]
  have hi := (ad.ofNatIsoRight i).homEquiv_leftAdjointUniq_hom_app Adjunction.id K
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hi
  rw [hi]
  exact (E.map_id K).trans
    ((bd.ofNatIsoRight j).homEquiv_leftAdjointUniq_hom_app Adjunction.id (E.obj K)).symm

private theorem derived_identity_square
    {C : Type a} [Category.{b} C] [Abelian C] [HasDerivedCategory C]
    {D : Type c} [Category.{d} D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (U : C ⥤ C) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (V : D ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (i : U ≅ 𝟭 C) (j : V ≅ 𝟭 D) (r : U ⋙ F ≅ F ⋙ V)
    (hr : ∀ N, F.map (i.hom.app N) = r.hom.app N ≫ j.hom.app (F.obj N))
    (K : DerivedCategory C) :
    F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K) =
      (Functor.mapDerivedCategorySquareIso r).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso j ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (F.mapDerivedCategory.obj K) := by
  have h : Functor.isoWhiskerRight i F = r ≪≫ Functor.isoWhiskerLeft F j := by
    apply Iso.ext
    ext N
    exact hr N
  have hi := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight i F) K
  have hj := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F j) K
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  have hv := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app] at hi hj hu hv
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U F).hom.app K)).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← hi, Category.assoc, hu]
  rw [← Category.assoc _ _ ((Functor.mapDerivedCategoryIdIso D).hom.app _), ← hj,
    Category.assoc, hv]
  rw [h, Functor.mapDerivedCategoryNatIso_trans]
  simp only [NatTrans.comp_app, Category.assoc]

private theorem derived_adjoint_identity_transport
    {C : Type a} [Category.{b} C] [Abelian C] [HasDerivedCategory C]
    {D : Type c} [Category.{d} D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (U : C ⥤ C) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (V : D ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {L : DerivedCategory C ⥤ DerivedCategory C}
    {M : DerivedCategory D ⥤ DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) (bd : M ⊣ V.mapDerivedCategory)
    (r : U ⋙ F ≅ F ⋙ V)
    (rD : U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ V.mapDerivedCategory)
    (t : L ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ M)
    (hD : rD = Functor.mapDerivedCategorySquareIso r)
    (hn : ∀ K N (f : L.obj K ⟶ N),
      F.mapDerivedCategory.map (ad.homEquiv K N f) ≫ rD.hom.app N =
        bd.homEquiv _ _ (t.inv.app K ≫ F.mapDerivedCategory.map f))
    (i : U ≅ 𝟭 C) (j : V ≅ 𝟭 D)
    (hr : ∀ N, F.map (i.hom.app N) = r.hom.app N ≫ j.hom.app (F.obj N))
    (K : DerivedCategory C) :
    F.mapDerivedCategory.map
        (((ad.ofNatIsoRight (Functor.mapDerivedCategoryNatIso i ≪≫
          Functor.mapDerivedCategoryIdIso C)).leftAdjointUniq Adjunction.id).hom.app K) =
      t.hom.app K ≫
        ((bd.ofNatIsoRight (Functor.mapDerivedCategoryNatIso j ≪≫
          Functor.mapDerivedCategoryIdIso D)).leftAdjointUniq Adjunction.id).hom.app
          (F.mapDerivedCategory.obj K) := by
  apply adjoint_identity_transport ad bd F.mapDerivedCategory rD t hn
  intro N
  rw [hD]
  exact derived_identity_square F U V i j r hr N

section RingedIdentity
universe q
variable {C : Type (q + 1)} [Category.{q} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{q + 1}]
  [(J.W (A := AddCommGrpCat.{q + 1})).IsMonoidal]
attribute [local semireducible] sectionModuleEquivalence Functor.mapDerivedCategory
open SheafOfModules
private theorem ringed_identity_transport
    (A : Sheaf J AddCommGrpCat.{q + 1}) [MonObj A] [IsCommMonObj A]
    (f : A ⟶ A) [IsMonHom f] (hf : f = 𝟙 A)
    (g : sectionRingSheaf.{q + 1, q + 1, q} J A ⟶
      sectionRingSheaf.{q + 1, q + 1, q} J A) (hg : g = 𝟙 _)
    (M : ScalarHomModels.{q + 1, q, q, q + 1} J)
    {L : DerivedCategory (Mod (Sheaf J AddCommGrpCat.{q + 1}) A) ⥤
      DerivedCategory (Mod (Sheaf J AddCommGrpCat.{q + 1}) A)}
    (ad : L ⊣ (Mod.comap (D := Sheaf J AddCommGrpCat.{q + 1}) f).mapDerivedCategory)
    (r : Mod.comap (D := Sheaf J AddCommGrpCat.{q + 1}) f ⋙
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor ≅
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor ⋙
        scalarRestriction.{q + 1, q, q + 1} g)
    (hr : ∀ (N : Mod (Sheaf J AddCommGrpCat.{q + 1}) A)
      (U : Cᵒᵖ) (x : N.X.obj.obj U), (r.hom.app N).val.app U x = x)
    (rD : (Mod.comap (D := Sheaf J AddCommGrpCat.{q + 1}) f).mapDerivedCategory ⋙
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory ≅
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory ⋙
        scalarDerivedRestriction.{q + 1, q, q + 1, q + 1} g)
    (t : L ⋙ (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory ≅
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory ⋙
        (M.scalar g).derived)
    (hD : rD = Functor.mapDerivedCategorySquareIso r)
    (hn : ∀ K N (k : L.obj K ⟶ N),
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory.map
          (ad.homEquiv K N k) ≫ rD.hom.app N =
        (M.scalar g).adjunction.homEquiv _ _
          (t.inv.app K ≫
            (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory.map k))
    (K : DerivedCategory (Mod (Sheaf J AddCommGrpCat.{q + 1}) A)) :
    (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory.map
        (((ad.ofNatIsoRight (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr hf ≪≫ Mod.comapId A) ≪≫
            Functor.mapDerivedCategoryIdIso _)).leftAdjointUniq Adjunction.id).hom.app K) =
      t.hom.app K ≫
        (eqToIso (congrArg (fun z ↦ (M.scalar z).derived) hg) ≪≫
          scalarHomExtensionId M (sectionRingSheaf.{q + 1, q + 1, q} J A)).hom.app
            ((sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.mapDerivedCategory.obj
              K) := by
  subst f
  subst g
  let i := Mod.comapCongr (show 𝟙 A = 𝟙 A from rfl) ≪≫ Mod.comapId A
  let j := scalarHomOrdinaryRestrictionId.{q + 1, q, q}
    (sectionRingSheaf.{q + 1, q + 1, q} J A)
  have hi (N : Mod (Sheaf J AddCommGrpCat.{q + 1}) A) :
      (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.map (i.hom.app N) =
        r.hom.app N ≫ j.hom.app
          ((sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor.obj N) := by
    ext U x
    change x = (r.hom.app N).val.app U x
    exact (hr N U x).symm
  have h := derived_adjoint_identity_transport
    (sectionModuleEquivalence.{q + 1, q + 1, q} J A).functor
    (Mod.comap (D := Sheaf J AddCommGrpCat.{q + 1}) (𝟙 A))
    (scalarRestriction.{q + 1, q, q + 1} (𝟙 _)) ad (M.scalar (𝟙 _)).adjunction
    r rD t hD hn i j hi K
  simp only [eqToIso_refl, Iso.refl_trans]
  unfold scalarHomExtensionId scalarHomRestrictionId
  exact h
end RingedIdentity

private theorem lowerBound_transport
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : DerivedCategory A) (b : ℤ) :
    K.IsGE b ↔ (F.mapDerivedCategory.obj K).IsGE b := by
  constructor
  · intro h
    exact F.isGE_mapDerivedCategory_obj K b
  · intro h
    apply (DerivedCategory.isGE_iff K b).2
    intro n hn
    exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff _ b).1 h n hn)


section ScalarMate
variable {C : Type a₀} [Category.{b₀} C] {D : Type a₁} [Category.{b₁} D]
variable (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
  (S : D ⥤ D ⥤ D) (J : Dᵒᵖ ⥤ D ⥤ D)
  (adj : T ⊣₂ H) (adj' : S ⊣₂ J) (F : C ⥤ D)
  (μ : (Functor.postcompose₂.obj F).obj T ≅
    (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S)
private abbrev scalarMate (K L : C) := scalarHomMate T H S J adj adj' F μ K L

private theorem scalarMate_naturality (K K' L L' : C) (f : K' ⟶ K) (g : L ⟶ L') :
    F.map (((H.map f.op).app L) ≫ (H.obj (op K')).map g) ≫
      scalarMate T H S J adj adj' F μ K' L' =
    scalarMate T H S J adj adj' F μ K L ≫
      (J.map (F.map f).op).app (F.obj L) ≫ (J.obj (op (F.obj K'))).map (F.map g) := by
  unfold scalarMate scalarHomMate
  rw [← adj'.homEquiv_naturality_two,
    ← adj'.homEquiv_naturality_one_assoc, ← adj'.homEquiv_naturality_three]
  apply congrArg adj'.homEquiv
  let A := (H.obj (op K)).obj L
  let A' := (H.obj (op K')).obj L'
  let h : A ⟶ A' := (H.map f.op).app L ≫ (H.obj (op K')).map g
  have hn : (S.obj (F.obj K')).map (F.map h) ≫ (μ.inv.app K').app A' =
      (μ.inv.app K').app A ≫ F.map ((T.obj K').map h) :=
    (μ.inv.app K').naturality h
  have hf : (S.map (F.map f)).app (F.obj A) ≫ (μ.inv.app K).app A =
      (μ.inv.app K').app A ≫ F.map ((T.map f).app A) :=
    NatTrans.congr_app (μ.inv.naturality f) A
  have hc : (T.obj K').map h ≫ (adj.adj K').counit.app L' =
      (T.map f).app A ≫ (adj.adj K).counit.app L ≫ g := by
    dsimp only [h]
    have hg := (adj.adj K').counit.naturality g
    change (T.obj K').map ((H.obj (op K')).map g) ≫
      (adj.adj K').counit.app L' = (adj.adj K').counit.app L ≫ g at hg
    rw [Functor.map_comp, Category.assoc, hg, ← Category.assoc]
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      A, Category.assoc] using
      congrArg (fun k ↦ k ≫ g)
      (NatTrans.congr_app (adj.whiskerLeft_map_counit f) L).symm
  change (S.obj (F.obj K')).map (F.map h) ≫
      (μ.inv.app K').app A' ≫ F.map ((adj.adj K').counit.app L') =
    ((S.map (F.map f)).app (F.obj A) ≫
      (μ.inv.app K).app A ≫ F.map ((adj.adj K).counit.app L)) ≫ F.map g
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, hc,
    F.map_comp, F.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← hf]
  simp only [Category.assoc]

end ScalarMate

private theorem post_transport
    {C : Type a₀} [Category.{b₀} C] {E : Type a₁} [Category.{b₁} E]
    {I : Type*} [Category I] [HasColimitsOfShape I C] [HasColimitsOfShape I E]
    (F : C ⥤ E) [PreservesColimitsOfShape I F]
    (G : C ⥤ C) (H : E ⥤ E) (σ : G ⋙ F ≅ F ⋙ H) (D : I ⥤ C) :
    F.map (colimit.post D G) ≫ σ.hom.app (colimit D) ≫
        H.map (preservesColimitIso F D).hom =
      (preservesColimitIso F (D ⋙ G)).hom ≫
        colimMap (Functor.isoWhiskerLeft D σ).hom ≫ colimit.post (D ⋙ F) H := by
  apply (isColimitOfPreserves F (colimit.isColimit (D ⋙ G))).hom_ext
  intro i
  change F.map (colimit.ι (D ⋙ G) i) ≫ _ = F.map (colimit.ι (D ⋙ G) i) ≫ _
  rw [← F.map_comp_assoc, colimit.ι_post,
    ι_preservesColimitIso_hom_assoc, ι_colimMap_assoc]
  change F.map (G.map (colimit.ι D i)) ≫ σ.hom.app (colimit D) ≫
      H.map (preservesColimitIso F D).hom =
    σ.hom.app (D.obj i) ≫ colimit.ι ((D ⋙ F) ⋙ H) i ≫ colimit.post (D ⋙ F) H
  rw [colimit.ι_post]
  change F.map (G.map (colimit.ι D i)) ≫ σ.hom.app (colimit D) ≫
      H.map (preservesColimitIso F D).hom =
    σ.hom.app (D.obj i) ≫ H.map (colimit.ι (D ⋙ F) i)
  have hn := σ.hom.naturality (colimit.ι D i)
  change F.map (G.map (colimit.ι D i)) ≫ σ.hom.app (colimit D) =
    σ.hom.app (D.obj i) ≫ H.map (F.map (colimit.ι D i)) at hn
  rw [← Category.assoc, hn, Category.assoc, ← H.map_comp,
    ι_preservesColimitIso_hom]

private theorem colimit_map_transport
    {C : Type a₀} [Category.{b₀} C] {E : Type a₁} [Category.{b₁} E]
    {I : Type*} [Category I] [HasColimitsOfShape I C] [HasColimitsOfShape I E]
    (F : C ⥤ E) [PreservesColimitsOfShape I F]
    (D E₀ : I ⥤ C) (D' E' : I ⥤ E)
    (d : D ⋙ F ≅ D') (e : E₀ ⋙ F ≅ E')
    (f : D ⟶ E₀) (g : D' ⟶ E')
    (h : Functor.whiskerRight f F ≫ e.hom = d.hom ≫ g) :
    F.map (colimMap f) ≫ (preservesColimitIso F E₀).hom ≫ colimMap e.hom =
      (preservesColimitIso F D).hom ≫ colimMap d.hom ≫ colimMap g := by
  have hn := (preservesColimitNatIso F).hom.naturality f
  change F.map (colimMap f) ≫ (preservesColimitIso F E₀).hom =
    (preservesColimitIso F D).hom ≫ colimMap (Functor.whiskerRight f F) at hn
  rw [← Category.assoc, hn, Category.assoc]
  apply congrArg (fun q ↦ (preservesColimitIso F D).hom ≫ q)
  change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
  rw [← Functor.map_comp, ← Functor.map_comp, h]

set_option backward.isDefEq.respectTransparency false in
private theorem post_quasiIso_transport
    {C : Type a₀} [Category.{b₀} C] [Abelian C]
    {E : Type a₁} [Category.{b₁} E] [Abelian E]
    {I : Type*} [Category I] [HasColimitsOfShape I C] [HasColimitsOfShape I E]
    (e : C ≌ E) [e.functor.Additive]
    (G : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (H : CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (σ : G ⋙ e.functor.mapHomologicalComplex (.up ℤ) ≅
      e.functor.mapHomologicalComplex (.up ℤ) ⋙ H)
    (D : I ⥤ CochainComplex C ℤ) :
    QuasiIso (colimit.post D G) ↔
      QuasiIso (colimit.post (D ⋙ e.functor.mapHomologicalComplex (.up ℤ)) H) := by
  let F := e.functor.mapHomologicalComplex (.up ℤ)
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (colimit.post D G) e.functor]
  exact quasiIso_iff_of_arrow_mk_iso
    (F.map (colimit.post D G)) (colimit.post (D ⋙ F) H)
    (Arrow.isoMk
      (preservesColimitIso F (D ⋙ G) ≪≫
        colim.mapIso (Functor.isoWhiskerLeft D σ))
      (σ.app (colimit D) ≪≫ H.mapIso (preservesColimitIso F D))
      (by
        change _ ≫ colimit.post (D ⋙ F) H = F.map (colimit.post D G) ≫ _
        simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, colimMap_eq,
          Iso.app_hom] using
          (post_transport F G H σ D).symm))

set_option backward.isDefEq.respectTransparency false in
private theorem post_quasiIso_diagram_iso
    {C : Type a₀} [Category.{b₀} C] [Abelian C]
    {I : Type*} [Category I] [HasColimitsOfShape I C]
    {D E : I ⥤ CochainComplex C ℤ} (e : D ≅ E)
    (H : CochainComplex C ℤ ⥤ CochainComplex C ℤ) :
    QuasiIso (colimit.post D H) ↔ QuasiIso (colimit.post E H) := by
  exact quasiIso_iff_of_arrow_mk_iso (colimit.post D H) (colimit.post E H)
    (Arrow.isoMk (colim.mapIso (Functor.isoWhiskerRight e H))
      (H.mapIso (colim.mapIso e)) (colimit.map_post e.hom H).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem continuity_equivalence
    {C : Type a₀} [Category.{b₀} C] [Abelian C]
    {E : Type a₁} [Category.{b₁} E] [Abelian E]
    [HasColimitsOfSize.{i, i} C] [HasColimitsOfSize.{i, i} E]
    (e : C ≌ E) [e.functor.Additive]
    (G : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (H : CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (σ : G ⋙ e.functor.mapHomologicalComplex (.up ℤ) ≅
      e.functor.mapHomologicalComplex (.up ℤ) ⋙ H)
    (bound : ∀ (P : CochainComplex C ℤ) (b : ℤ),
      (∀ n : ℤ, n < b → IsZero (P.X n)) ↔
        ∀ n : ℤ, n < b →
          IsZero (((e.functor.mapHomologicalComplex (.up ℤ)).obj P).X n)) :
    (∀ (I : Type i) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ CochainComplex C ℤ) (b : ℤ),
      (∀ (j : I) (n : ℤ), n < b → IsZero ((D.obj j).X n)) →
        QuasiIso (colimit.post D G)) ↔
    (∀ (I : Type i) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ CochainComplex E ℤ) (b : ℤ),
      (∀ (j : I) (n : ℤ), n < b → IsZero ((D.obj j).X n)) →
        QuasiIso (colimit.post D H)) := by
  let ec := e.mapHomologicalComplex (.up ℤ)
  constructor
  · intro h I _ _ D b hb
    let D₀ := D ⋙ ec.inverse
    have he : D₀ ⋙ ec.functor ≅ D := Functor.isoWhiskerLeft D ec.counitIso
    have hb₀ (j : I) : ∀ n : ℤ, n < b → IsZero ((D₀.obj j).X n) := by
      apply (bound (D₀.obj j) b).2
      intro n hn
      exact (hb j n hn).of_iso
        ((HomologicalComplex.eval _ _ n).mapIso (he.app j))
    exact (post_quasiIso_diagram_iso he H).1
      ((post_quasiIso_transport e G H σ D₀).1 (h I D₀ b hb₀))
  · intro h I _ _ D b hb
    apply (post_quasiIso_transport e G H σ D).2
    apply h I (D ⋙ ec.functor) b
    intro j
    exact (bound (D.obj j) b).1 (hb j)


universe a₂ b₂ a₃ b₃

-- Normalize identities before instantiating the localization with concrete module sheaves.
private theorem resolutionNaturality
    {C₀ : Type a₀} [Category.{b₀} C₀] {C : Type a₂} [Category.{b₂} C]
    (q : C₀ ⥤ C) (I : C₀ ⥤ C₀) (H : Cᵒᵖ × C ⥤ C) (J : C₀ᵒᵖ ⥤ C₀ ⥤ C₀)
    (c : q.op.prod q ⋙ H ≅ (𝟭 _).prod I ⋙ Functor.uncurry.obj J ⋙ q)
    (P N N' : C₀) (g : N ⟶ N') :
    H.map (Prod.mkHom (𝟙 (op (q.obj P))) (q.map g)) ≫ c.hom.app (op P, N') =
      c.hom.app (op P, N) ≫ q.map ((J.obj (op P)).map (I.map g)) := by
  have ht := c.hom.naturality (Prod.mkHom (𝟙 (op P)) g)
  change H.map (Prod.mkHom (q.map (𝟙 P)).op (q.map g)) ≫ c.hom.app (op P, N') =
    c.hom.app (op P, N) ≫ q.map ((J.map (𝟙 (op P))).app (I.obj N) ≫
      (J.obj (op P)).map (I.map g)) at ht
  rw [q.map_id, op_id, J.map_id, NatTrans.id_app] at ht
  rw [Category.id_comp ((J.obj (op P)).map (I.map g))] at ht
  exact ht

section CoefficientResolutionNaturality
universe q
open SheafOfModules
variable {C : Type (q + 1)} [Category.{q} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{q + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{q + 1}]
private theorem coefficient_resolution_naturality
    (A : Sheaf J CommRingCat.{q + 1})
    (P N N' : CochainComplex (SheafOfModules.{q + 1}
      ((sheafCompose J (forget₂ CommRingCat.{q + 1} RingCat.{q + 1})).obj A)) ℤ)
    (g : N ⟶ N') :
    ((Functor.curry.obj (derivedInternalHomOfUniverses.{q + 1, q, q, q + 1} J A)).obj
        (op (DerivedCategory.Q.obj P))).map (DerivedCategory.Q.map g) ≫
        (coefficientHomResolutionIso.{q, q + 1, q, q + 1} J A P N').hom =
      (coefficientHomResolutionIso.{q, q + 1, q, q + 1} J A P N).hom ≫
        DerivedCategory.Q.map
          ((SfbHomFilteredColimit.homFixed.{q + 1, q, q} J A P).map g) := by
  let Q : CochainComplex (SheafOfModules.{q + 1}
      ((sheafCompose J (forget₂ CommRingCat.{q + 1} RingCat.{q + 1})).obj A)) ℤ ⥤
      DerivedCategory.{q + 1} (SheafOfModules.{q + 1}
        ((sheafCompose J (forget₂ CommRingCat.{q + 1} RingCat.{q + 1})).obj A)) :=
    DerivedCategory.Q
  let : IsGrothendieckAbelian.{q + 1} (SheafOfModules.{q + 1}
      ((sheafCompose J (forget₂ CommRingCat.{q + 1} RingCat.{q + 1})).obj A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{q + 1, q, q}
      J A).1
  let c := Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{q + 1} _) ⋙
      Functor.uncurry.obj (homComplexFunctor.{q + 1, q, q + 1, q + 1} (R := A)) ⋙ Q)
    (derivedInternalHomOfUniverses_inverts.{q + 1, q, q, q + 1} J A _
      (CochainComplex.toKInjectiveResolution.{q + 1} _)
      (fun N ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{q + 1}
        _ N).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{q + 1}
          _ N⟩)) (Q.op.prod Q)
  have ht := resolutionNaturality Q
    (CochainComplex.kInjectiveResolutionFunctor.{q + 1} _) _
    (homComplexFunctor.{q + 1, q, q + 1, q + 1} (R := A)) c P N N' g
  exact ht
end CoefficientResolutionNaturality

-- Lift the entire representative isomorphism and retain its prescribed component square.
private theorem representativeComparison
    {C₀ : Type a₀} [Category.{b₀} C₀] {D₀ : Type a₁} [Category.{b₁} D₀]
    {C : Type a₂} [Category.{b₂} C] {D : Type a₃} [Category.{b₃} D]
    (q : C₀ ⥤ C) (q' : D₀ ⥤ D) (f : C₀ ⥤ D₀) (F : C ⥤ D)
    [F.Full] [F.Faithful] (l : q ⋙ F ≅ f ⋙ q')
    (H : Cᵒᵖ ⥤ C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (θ : Functor.uncurry.obj H ⋙ F ≅ F.op.prod F ⋙ J)
    (G : C₀ ⥤ C₀) (G' : D₀ ⥤ D₀) (σ : G ⋙ f ≅ f ⋙ G')
    (P : C₀) (ρ : q' ⋙ (Functor.curry.obj J).obj (op (q'.obj (f.obj P))) ≅ G' ⋙ q') :
    ∃ j : G ⋙ q ≅ q ⋙ H.obj (op (q.obj P)),
      ∀ N : C₀,
        F.map (j.hom.app N) ≫ θ.hom.app (op (q.obj P), q.obj N) ≫
          J.map (X := (op (F.obj (q.obj P)), F.obj (q.obj N)))
            (Y := (op (q'.obj (f.obj P)), q'.obj (f.obj N)))
            ((l.inv.app P).op, l.hom.app N) ≫ ρ.hom.app (f.obj N) =
        l.hom.app (G.obj N) ≫ q'.map (σ.hom.app N) := by
  let A := H.obj (op (q.obj P))
  let B := (Functor.curry.obj J).obj (op (q'.obj (f.obj P)))
  let e : (q ⋙ A) ⋙ F ≅ (f ⋙ q') ⋙ B :=
    NatIso.ofComponents (fun N ↦ θ.app (op (q.obj P), q.obj N) ≪≫
      J.mapIso ((l.app P).symm.op.prod (l.app N))) (by
      intro N N' g
      have hθ : F.map (A.map (q.map g)) ≫ θ.hom.app (op (q.obj P), q.obj N') =
          θ.hom.app (op (q.obj P), q.obj N) ≫
            J.map (Prod.mkHom (𝟙 (op (F.obj (q.obj P)))) (F.map (q.map g))) := by
        have ht := θ.hom.naturality (Prod.mkHom (𝟙 (op (q.obj P))) (q.map g))
        dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map,
          Functor.uncurry_obj_map, Prod.mkHom] at ht
        rw [unop_id, F.map_id, op_id, H.map_id] at ht
        simpa only [A, NatTrans.id_app, Category.id_comp] using ht
      have hl := l.hom.naturality g
      change F.map (A.map (q.map g)) ≫
          (θ.hom.app (op (q.obj P), q.obj N') ≫
            J.map (Prod.mkHom (l.inv.app P).op (l.hom.app N'))) =
        (θ.hom.app (op (q.obj P), q.obj N) ≫
          J.map (Prod.mkHom (l.inv.app P).op (l.hom.app N))) ≫
            J.map (Prod.mkHom (𝟙 (op (q'.obj (f.obj P)))) (q'.map (f.map g)))
      rw [← Category.assoc, hθ, Category.assoc, ← J.map_comp, Category.assoc, ← J.map_comp]
      congr 2
      ext
      · simp
      · exact hl)
  let d : (G ⋙ q) ⋙ F ≅ (f ⋙ q') ⋙ B :=
    Functor.isoWhiskerLeft G l ≪≫ Functor.isoWhiskerRight σ q' ≪≫
      Functor.isoWhiskerLeft f ρ.symm
  let j : G ⋙ q ≅ q ⋙ A := Functor.fullyFaithfulCancelRight F (d ≪≫ e.symm)
  refine ⟨j, ?_⟩
  intro N
  have hj : F.map (j.hom.app N) = d.hom.app N ≫ e.inv.app N := by
    dsimp only [j]
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    rfl
  rw [hj]
  have he : θ.hom.app (op (q.obj P), q.obj N) ≫
      J.map (X := (op (F.obj (q.obj P)), F.obj (q.obj N)))
        (Y := (op (q'.obj (f.obj P)), q'.obj (f.obj N)))
        ((l.inv.app P).op, l.hom.app N) = e.hom.app N := rfl
  rw [← Category.assoc _ _ (ρ.hom.app (f.obj N)), he]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  dsimp only [d, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun v ↦ l.hom.app (G.obj N) ≫ v)
    (Category.comp_id (q'.map (σ.hom.app N)))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- Normalized presentations exist for every prescribed ordinary ringed-site model.
Source: Stacks 08J9, 0A95
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: step 3 of the DAG applies moduleObject_ringedSite_derived_comparison.
The K-flat representative normalizations identify its tensor with the prescribed
one. Uniqueness of the parametrized right adjoint identifies its Hom with the
prescribed K-injective model, and its counit gives the evaluation equation. -/
theorem homPresentation_nonempty
    (S : CoefficientClosedStructure (hom.{u} Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) S) : Nonempty (HomPresentation.{u} Λ X S T) := by
  sorry

/-- Every common termwise lower bound, including all diagrams, is unchanged.
Source: Stacks 010N, 03CV
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: reconstruction fixes the underlying abelian sheaf in each degree, and
its exact inverse reflects zero objects (DAG step 1). Apply this at each degree. -/
theorem termwise_lower_bound_iff (P : CochainComplex (Internal.{u} Λ X) ℤ) (b : ℤ) :
    (∀ n : ℤ, n < b → IsZero (P.X n)) ↔
      ∀ n : ℤ, n < b → IsZero (((complexForward.{u} Λ X).obj P).X n) := by
  have hz (N : Internal.{u} Λ X) :
      IsZero N ↔ IsZero ((sectionForward.{u} Λ X).obj N) := by
    simp only [IsZero.iff_id_eq_zero]
    rw [← (sectionForward.{u} Λ X).map_id,
      (sectionForward.{u} Λ X).map_eq_zero_iff]
  exact forall_congr' fun n ↦ forall_congr' fun _ ↦ hz (P.X n)

/-- The derived equivalence preserves and reflects every cohomological lower bound.
Source: Stacks 010N
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: exact-functor cohomology identifies the image of every cohomology object
with cohomology of the image. The equivalence preserves and reflects zero
objects; apply this in each degree below b (DAG step 1). -/
theorem cohomological_lower_bound_iff (K : DerivedCategory.{u + 1} (Internal.{u} Λ X)) (b : ℤ) :
    K.IsGE b ↔ ((forward.{u} Λ X).obj K).IsGE b := by
  have : (sectionForward.{u} Λ X).Additive := inferInstance
  exact lowerBound_transport (sectionForward.{u} Λ X) K b

/-- The transported representatives really compute the native derived Hom.
Source: Stacks 08J9, 0A95
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: localize the representative counit and use localizationIso. The fixed
coefficientHomResolutionIso identifies the section representative with section
Hom; HomPresentation.homIso identifies that with the image of native Hom.
Full faithfulness of the derived equivalence lifts this composite, naturally
in the second complex. This is DAG steps 3 and 4. -/
theorem internalHomRepresentative_computes
    (S : CoefficientClosedStructure (hom.{u} Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) S)
    (H : HomPresentation.{u} Λ X S T)
    (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    RepresentativeComputes.{u} Λ X S T H P := by
  let f := complexForward.{u} Λ X
  let B := (Functor.curry.obj (hom.{u} Λ X)).obj
    (op (DerivedCategory.Q.obj (f.obj P)))
  let q' : CochainComplex (Modules.{u} Λ X) ℤ ⥤
      DerivedCategory.{u + 1} (Modules.{u} Λ X) := DerivedCategory.Q
  let ρ : q' ⋙ B ≅
      SfbHomFilteredColimit.homFixed.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring.{u} Λ X) (f.obj P) ⋙ q' :=
    NatIso.ofComponents (fun N ↦ coefficientHomResolutionIso.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) (f.obj P) N) (by
      intro N N' g
      exact coefficient_resolution_naturality (Scheme.ProEt.topology X)
        (ring.{u} Λ X) (f.obj P) N N' g)
  let : (forward.{u} Λ X).Full :=
    inferInstanceAs (equivalence.{u} Λ X).mapDerivedCategory.functor.Full
  let : (forward.{u} Λ X).Faithful :=
    inferInstanceAs (equivalence.{u} Λ X).mapDerivedCategory.functor.Faithful
  dsimp only [RepresentativeComputes, homRepresentativeSquare]
  have h := representativeComparison DerivedCategory.Q q' f (forward.{u} Λ X)
      (localizationIso.{u} Λ X)
      (CondensedRing.derivedHom.{u} Λ X) (hom.{u} Λ X) H.homIso
      (internalHomRepresentative.{u} Λ X P)
      (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring.{u} Λ X) (f.obj P))
      (homRepresentativeIso.{u} Λ X P) P ρ
  exact h

attribute [local irreducible] SfbHomFilteredColimit.homFixed

/-- The two continuity arrows themselves are conjugate by the representative and
colimit comparisons. No continuity assumption on P occurs.
Source: Stacks 03DB, 08J9, 0A95; Categories Tag 002F
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG steps 2 and 4. The exact equivalence transports the actual termwise
colimit cocone with its legs. Naturality of the counit identifies each Hom leg.
Degreewise uniqueness of the colimit mediator identifies the induced chain maps.
Exact filtered colimits preserve quasi-isomorphisms, so localization gives the
same equation for derived Hom, without bounding P or its Hom complex. -/
theorem continuity_map_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : CochainComplex (Internal.{u} Λ X) ℤ)
    (D : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ) (b : ℤ)
    (_h : ∀ (i : I) (n : ℤ), n < b → IsZero ((D.obj i).X n)) :
    PostComparisonSquare (complexForward.{u} Λ X)
      (internalHomRepresentative.{u} Λ X P)
      (SfbHomFilteredColimit.homFixed.{u + 1, u, u} (Scheme.ProEt.topology X)
        (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))
      (homRepresentativeIso.{u} Λ X P) D := by
  exact post_transport (complexForward.{u} Λ X) (internalHomRepresentative.{u} Λ X P)
    (SfbHomFilteredColimit.homFixed.{u + 1, u, u} (Scheme.ProEt.topology X)
      (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))
    (homRepresentativeIso.{u} Λ X P) D

/-- Continuity for all small filtered diagrams with a common termwise lower bound
is equivalent in the two presentations, for arbitrary first input P.
Source: Stacks 03DB, 08J9, 0A95
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: step 4 uses continuity_map_transport, preservation and reflection of
quasi-isomorphisms and the termwise bound. Every section diagram transports back
through the inverse equivalence with its cocone; its counit recovers the diagram.
Thus the implication holds both ways, without bounding the first input. -/
theorem continuity_iff (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    BoundedFilteredContinuity.{_, _, u + 1} (internalHomRepresentative.{u} Λ X P) ↔
      BoundedFilteredContinuity.{_, _, u + 1}
        (SfbHomFilteredColimit.homFixed.{u + 1, u, u} (Scheme.ProEt.topology X)
          (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P)) := by
  have : (sectionForward.{u} Λ X).asEquivalence.functor.Additive := by
    change (sectionForward.{u} Λ X).Additive
    infer_instance
  exact continuity_equivalence.{_, _, _, _, u + 1} (sectionForward.{u} Λ X).asEquivalence
    (internalHomRepresentative.{u} Λ X P)
    (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))
    (homRepresentativeIso.{u} Λ X P) (termwise_lower_bound_iff Λ X)

/-- Finite freeness is invariant, with the same rank, including rank zero.
Source: Stacks 03EK (blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 10. The exact equivalence preserves finite sums and identifies
the regular module with the section-ring regular module by the normalized unit
comparison. Apply it and its inverse to the given finite-free isomorphism. -/
theorem finite_free_iff (N : Internal.{u} Λ X) (n : ℕ) :
    Nonempty (N ≅ ∐ (fun _ : Fin n ↦ Mod.regular (condensedRingObj.{u} Λ X))) ↔
      Nonempty ((equivalence.{u} Λ X).functor.obj N ≅
        ∐ (fun _ : Fin n ↦ SheafOfModules.unit
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring.{u} Λ X)))) := by
  have : IsCommMonObj (condensedRingObj.{u} Λ X) :=
    isCommMonObj_condensedRingObj Λ X
  let F := (equivalence.{u} Λ X).functor
  obtain ⟨_, _, e₀, _⟩ := internal_section_tensor_comparison
    (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X)
  let e : F.obj (∐ (fun _ : Fin n ↦ Mod.regular (condensedRingObj.{u} Λ X))) ≅
      ∐ (fun _ : Fin n ↦ SheafOfModules.unit
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring.{u} Λ X))) :=
    PreservesCoproduct.iso F _ ≪≫ Sigma.mapIso (fun _ ↦ e₀)
  constructor
  · rintro ⟨i⟩
    exact ⟨F.mapIso i ≪≫ e⟩
  · rintro ⟨i⟩
    exact ⟨F.preimageIso (i ≪≫ e.symm)⟩

/-- Reconstruction transports a specified module cocone, without changing its legs.
Source: Stacks 03DB; Categories 002F
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 2. Apply the inverse equivalence to a target cocone, factor uniquely
through the given colimit, then apply the forward equivalence. The unit and counit
make this construction inverse on mediators, giving preservation and reflection. -/
theorem module_colimit_iff {I : Type (u + 1)} [SmallCategory I]
    {D : I ⥤ Internal.{u} Λ X} (c : Cocone D) :
    Nonempty (IsColimit c) ↔
      Nonempty (IsColimit ((equivalence.{u} Λ X).functor.mapCocone c)) := by
  constructor
  · rintro ⟨hc⟩
    exact ⟨isColimitOfPreserves (equivalence.{u} Λ X).functor hc⟩
  · rintro ⟨hc⟩
    exact ⟨isColimitOfReflects (equivalence.{u} Λ X).functor hc⟩

/-- The map induced by a specified module cocone is the same transported map.
Source: Categories 002F (blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: both composites with each specified leg are the transported cocone leg.
Uniqueness of the colimit mediator gives equality (DAG step 2). -/
theorem module_colimit_desc {I : Type (u + 1)} [SmallCategory I]
    {D : I ⥤ Internal.{u} Λ X} {c : Cocone D} (hc : IsColimit c) (d : Cocone D) :
    (equivalence.{u} Λ X).functor.map (hc.desc d) =
      (isColimitOfPreserves (equivalence.{u} Λ X).functor hc).desc
        ((equivalence.{u} Λ X).functor.mapCocone d) := by
  exact (preserves_desc_mapCocone (equivalence.{u} Λ X).functor D _ _ hc).symm

/-- Every induced map on termwise filtered colimits is the transported map.
This applies to whole coefficient-evaluation representative diagrams, including
all their transition squares; the two natural transformations specify the maps.
Source: Stacks 03DB, 0A95; Categories 002F
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG steps 2 and 9. Precompose both paths with each colimit leg. Naturality
of the specified diagram comparisons and their square give the same chain map.
Uniqueness of the degreewise colimit mediator gives the equality. No assertion
that the evaluation maps or these induced maps are invertible is made. -/
theorem filtered_colimit_map_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D E : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ)
    (D' E' : I ⥤ CochainComplex (Modules.{u} Λ X) ℤ)
    (d : D ⋙ complexForward.{u} Λ X ≅ D')
    (e : E ⋙ complexForward.{u} Λ X ≅ E')
    (f : D ⟶ E) (g : D' ⟶ E')
    (h : Functor.whiskerRight f (complexForward.{u} Λ X) ≫ e.hom = d.hom ≫ g) :
    ColimitMapSquare (complexForward.{u} Λ X) D E D' E' d e f g := by
  exact colimit_map_transport (complexForward.{u} Λ X) D E D' E' d e f g h

section AlgebraColimits
open MonObj
open scoped TensorProduct

-- Reconstruct ring maps first on abelian groups, then on presheaves and sheaves.
@[irreducible]
private def commMonToRingFF : commMonToRing.{u}.FullyFaithful where
  preimage {R S} f := by
    letI := commRing R.X
    letI := commRing S.X
    let g : R.X ⟶ S.X := AddCommGrpCat.ofHom f.hom.toAddMonoidHom
    have : IsMonHom g := by
      constructor
      · apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro ⟨n⟩
        have h (T : CommMon AddCommGrpCat.{u}) :
            (η[T.X]).hom (ULift.up n) = n • (η[T.X]).hom (ULift.up 1) := by
          rw [← map_zsmul]
          congr 1
          change (ULift.up n : ULift.{u} ℤ) = n • ULift.up 1
          apply ULift.ext
          simp
        change f.hom ((η[R.X]).hom (ULift.up n)) = (η[S.X]).hom (ULift.up n)
        rw [h R, h S, map_zsmul]
        exact congrArg (fun x ↦ n • x) f.hom.map_one
      · exact AddCommGrpCat.hom_ext_toIntLinearMap
          (TensorProduct.ext' fun a b ↦ (map_mul f.hom a b :))
    exact CommMon.homMk (Mon.Hom.mk' g (IsMonHom.one_hom g) (IsMonHom.mul_hom g))
  map_preimage f := by ext x; rfl
  preimage_map f := by apply CommMon.hom_ext; ext x; rfl

@[irreducible]
private def ringInclusionFF (X : Scheme.{u}) :
    (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapCommMon.FullyFaithful
    where
  preimage {R S} f := by
    let F := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
    let g := F.preimage f.hom.hom
    have : IsMonHom (F.map g) := by rw [Functor.map_preimage]; infer_instance
    have : IsMonHom g := Sheaf.isMonHom_of_isMonHom_map (J := Scheme.ProEt.topology X)
      (A := AddCommGrpCat.{u + 1}) g
    exact CommMon.homMk (Mon.Hom.mk' g (IsMonHom.one_hom g) (IsMonHom.mul_hom g))
  map_preimage f := by
    apply CommMon.hom_ext
    exact (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map_preimage
      f.hom.hom
  preimage_map f := by
    apply CommMon.hom_ext
    exact Functor.preimage_map (F :=
      sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) f.hom.hom

@[irreducible]
private def sectionRingFF (X : Scheme.{u}) : (sectionRingFunctor.{u} X).FullyFaithful := by
  let I := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
  let E := Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.ProEtᵒᵖ
    (CommMon AddCommGrpCat.{u + 1}) CommRingCat.{u + 1}).obj commMonToRing
  let B := I.mapCommMon ⋙ E.functor ⋙ W
  let hB : B.FullyFaithful := (ringInclusionFF X).comp
    ((Functor.FullyFaithful.ofFullyFaithful E.functor).comp
      (commMonToRingFF.whiskeringRight X.ProEtᵒᵖ))
  let T := sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}
  have h : sectionRingFunctor.{u} X ⋙ T = B := rfl
  have : B.Full := hB.full
  have : B.Faithful := hB.faithful
  have : (sectionRingFunctor.{u} X).Full :=
    Functor.Full.of_comp_faithful_iso (eqToIso h)
  have : (sectionRingFunctor.{u} X).Faithful := Functor.Faithful.of_comp_eq h
  exact Functor.FullyFaithful.ofFullyFaithful _

private theorem sectionRingEssSurj (X : Scheme.{u}) :
    (sectionRingFunctor.{u} X).EssSurj := by
  let J := Scheme.ProEt.topology X
  let I := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let E := Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.ProEtᵒᵖ
    (CommMon AddCommGrpCat.{u + 1}) CommRingCat.{u + 1}).obj commMonToRing
  constructor
  intro S
  let S' := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj S'
  let m : MonObj A := Sheaf.monObj_sheafCompose_obj J S'
  have hc : IsCommMonObj A :=
    Sheaf.isCommMonObj_sheafCompose_obj J S' (fun U a b ↦ @mul_comm (S.obj.obj U) _ a b)
  let B : CommMon (Sheaf J AddCommGrpCat.{u + 1}) := CommMon.mk A
  let mp : MonObj A.obj := S'.obj.monObjCompForget₂
  have hcp : @IsCommMonObj _ _ _ _ A.obj mp :=
    S'.obj.isCommMonObj_compForget₂ (fun U a b ↦ @mul_comm (S.obj.obj U) _ a b)
  let P : CommMon (X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) := @CommMon.mk _ _ _ _ A.obj mp hcp
  let c : I.mapCommMon.obj B ≅ P := CommMon.mkIso (Iso.refl A.obj)
    (by
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact Sheaf.ε_comp_map_one A)
    (by
      change (Functor.LaxMonoidal.μ I A A ≫ I.map m.mul) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ mp.mul
      rw [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
      exact Sheaf.μ_comp_map_mul A)
  let z : (E.functor ⋙ W).obj P ≅ S.obj :=
    NatIso.ofComponents (fun U ↦ by
      let T := (E.functor.obj P).obj U
      letI := commRing T.X
      exact RingEquiv.toCommRingCatIso
        ({ Equiv.refl (S.obj.obj U) with
          map_mul' := fun _ _ ↦ rfl
          map_add' := fun _ _ ↦ rfl } : T.X ≃+* S.obj.obj U))
      (by intros; ext x; rfl)
  refine ⟨B, ⟨?_⟩⟩
  exact (sheafToPresheaf J CommRingCat.{u + 1}).preimageIso
    ((E.functor ⋙ W).mapIso c ≪≫ z)

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- Algebra cocones are reconstructed over the same base with the specified maps.
Here an algebra is an object under its base commutative ring object.
Source: Stacks 03EK; Categories 002F
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 10. Reconstruction and its inverse preserve multiplication, unit
and every section map. Thus a compatible algebra cocone with any vertex is the
same cocone in section notation. They give inverse bijections on mediators,
preserving the leg equations, so the colimit universal properties are equivalent. -/
theorem algebra_colimit_iff
    (B : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}))
    {I : Type (u + 1)} [SmallCategory I] {D : I ⥤ Under B} (c : Cocone D) :
    Nonempty (IsColimit c) ↔
      Nonempty (IsColimit ((Under.post (sectionRingFunctor.{u} X)).mapCocone c)) := by
  have : (sectionRingFunctor.{u} X).Full := (sectionRingFF X).full
  have : (sectionRingFunctor.{u} X).Faithful := (sectionRingFF X).faithful
  have : (sectionRingFunctor.{u} X).EssSurj := sectionRingEssSurj X
  have : (sectionRingFunctor.{u} X).IsEquivalence := {}
  constructor
  · rintro ⟨hc⟩
    exact ⟨isColimitOfPreserves (Under.post (sectionRingFunctor.{u} X)) hc⟩
  · rintro ⟨hc⟩
    exact ⟨isColimitOfReflects (Under.post (sectionRingFunctor.{u} X)) hc⟩

/-- The induced algebra mediator retains the specified maps.
Source: Stacks 03EK; Categories 002F
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: reconstruction leaves each section ring and ring-map operation unchanged.
Both maps have the same composites with every specified leg; the colimit
universal property gives equality, as in DAG step 10. -/
theorem algebra_colimit_desc
    (B : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}))
    {I : Type (u + 1)} [SmallCategory I] {D : I ⥤ Under B}
    {c : Cocone D} (hc : IsColimit c) (d : Cocone D)
    (hc' : IsColimit ((Under.post (sectionRingFunctor.{u} X)).mapCocone c)) :
    (Under.post (sectionRingFunctor.{u} X)).map (hc.desc d) =
      hc'.desc ((Under.post (sectionRingFunctor.{u} X)).mapCocone d) := by
  apply hc'.hom_ext
  intro i
  change (Under.post (sectionRingFunctor.{u} X)).map (c.ι.app i) ≫ _ = _
  rw [← Functor.map_comp, hc.fac]
  exact (hc'.fac ((Under.post (sectionRingFunctor.{u} X)).mapCocone d) i).symm

end AlgebraColimits

/-- Exact coefficient extension is closed under composition.
Source: Stacks 07A6, 03EK
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: ordinary extension along the composite is canonically isomorphic to the
composite extensions, by their restriction adjunctions. A composite of exact
functors is exact, and exactness is invariant under natural isomorphism. -/
theorem internalScalarComposite_exact
    {Γ Δ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
    [MonObj Γ] [IsCommMonObj Γ] [MonObj Δ] [IsCommMonObj Δ]
    (a : Λ ⟶ Γ) [IsMonHom a] (b : Γ ⟶ Δ) [IsMonHom b]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} a Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} b Z))]
    (Z : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} (a ≫ b) Z)) := by
  let e := Mod.extendScalarsIsoOfEq (coefficientMap_comp a b Z) ≪≫
      Mod.extendScalarsComp (coefficientMap.{u} a Z) (coefficientMap.{u} b Z)
  exact preservesFiniteLimits_of_natIso e.symm

/-- Identity coefficient extension is exact, including on the empty scheme.
Source: Stacks 07A6
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: ordinary identity extension is the identity by uniqueness of left adjoints
of identity restriction. Transport preservation of finite limits along that iso. -/
@[instance] theorem internalScalarIdentity_exact (Z : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} (𝟙 Λ) Z)) := by
  let e : Mod.extendScalars (coefficientMap.{u} (𝟙 Λ) Z) ≅
      𝟭 (Internal.{u} Λ Z) :=
    Mod.extendScalarsIsoOfEq (coefficientMap_id Z) ≪≫
      Mod.extendScalarsId (R := condensedRingObj.{u} Λ Z)
  exact preservesFiniteLimits_of_natIso e.symm

/-- Identity scalar Hom is the identity under the actual scalar unitor.
Source: Stacks 07A4, 08J9
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 7 identifies the scalar unitor through its unit normalization.
Transpose the identity-coefficient scalar Hom map; after the unitor it is
ordinary evaluation. The closed adjunction bijection is injective. -/
theorem internalScalarHom_identity
    (K L : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    internalScalarHom.{u} (𝟙 Λ) K L ≫
      (Functor.uncurry.obj (CondensedRing.derivedHom.{u} Λ X)).map
        (Prod.mkHom ((internalExtensionId.{u} Λ X).inv.app K).op
          ((internalExtensionId.{u} Λ X).hom.app L)) =
      (internalExtensionId.{u} Λ X).hom.app
        (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) := by
  sorry

attribute [local irreducible] CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

section Scalar
variable {X}
variable {Λ}
variable {Γ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
  [MonObj Γ] [IsCommMonObj Γ] (a : Λ ⟶ Γ) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} a Z))]

-- Retain the recorded exactness binder in the public interface.
set_option linter.unusedSectionVars false in
/-- The native comparison is natural for all derived morphisms in both inputs.
Source: Stacks 07A4, 08J9
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 7. Transpose the equation under the native closed adjunction.
Naturality of the scalar tensor comparison, evaluation and scalar extension
makes the two transposes equal. Injectivity of the adjunction bijection gives
the equation, including inverses of localized quasi-isomorphisms. -/
theorem internalScalarHom_naturality
    (K K' L L' : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (f : K' ⟶ K) (g : L ⟶ L') :
    (CondensedRing.internalScalarExtension.{u} a X).map
        (((CondensedRing.derivedHom.{u} Λ X).map f.op).app L ≫
          ((CondensedRing.derivedHom.{u} Λ X).obj (op K')).map g) ≫
        internalScalarHom.{u} a K' L' =
      internalScalarHom.{u} a K L ≫
        ((CondensedRing.derivedHom.{u} Γ X).map
          ((CondensedRing.internalScalarExtension.{u} a X).map f).op).app
            ((CondensedRing.internalScalarExtension.{u} a X).obj L) ≫
        ((CondensedRing.derivedHom.{u} Γ X).obj
          (op ((CondensedRing.internalScalarExtension.{u} a X).obj K'))).map
            ((CondensedRing.internalScalarExtension.{u} a X).map g) := by
  exact scalarMate_naturality
    (CondensedRing.derivedTensor.{u} Λ X) (CondensedRing.derivedHom.{u} Λ X)
    (CondensedRing.derivedTensor.{u} Γ X) (CondensedRing.derivedHom.{u} Γ X)
    (CondensedRing.derivedTensorHomAdjunction₂.{u} Λ X)
    (CondensedRing.derivedTensorHomAdjunction₂.{u} Γ X)
    (CondensedRing.internalScalarExtension.{u} a X)
    (CondensedRing.internalScalarTensorIso.{u} a X) K K' L L' f g

-- Keep the scalar constructions folded while checking the remaining comparison statements.
attribute [local irreducible] internalScalarHom internalRestrictedHom
  internalExtensionComp internalExtensionId

/-- Successive internal evaluation-transpose maps equal the direct comparison.
Source: Stacks 07A4, 08J9, 0D6D
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 7. The scalar compositor is fixed by the actual adjunction units.
On K-flat tensors it sends t tensor (s tensor x) to t b(s) tensor x.
Transpose both sides: scalar tensor coherence and evaluation naturality identify
both with the same extended evaluation. Injectivity gives the equation. -/
theorem internalScalarHom_composition
    {Δ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
    [MonObj Δ] [IsCommMonObj Δ] (b : Γ ⟶ Δ) [IsMonHom b]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} b Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap.{u} (a ≫ b) Z))]
    (K L : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    (CondensedRing.internalScalarExtension.{u} b X).map (internalScalarHom.{u} a K L) ≫
      internalScalarHom.{u} b
        ((CondensedRing.internalScalarExtension.{u} a X).obj K)
        ((CondensedRing.internalScalarExtension.{u} a X).obj L) ≫
      (Functor.uncurry.obj (CondensedRing.derivedHom.{u} Δ X)).map
        (Prod.mkHom ((internalExtensionComp.{u} (X := X) a b).inv.app K).op
          ((internalExtensionComp.{u} (X := X) a b).hom.app L)) =
      (internalExtensionComp.{u} (X := X) a b).hom.app
          (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
        internalScalarHom.{u} (a ≫ b) K L := by
  sorry

variable (X)
  (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
  (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S),
    ScalarHomTensorComparison.{u + 1, u, u, u + 1} M f)
  (PΛ : HomPresentation.{u} Λ X (M.closed (ring.{u} Λ X)) (M.model (ring.{u} Λ X)))
  (PΓ : HomPresentation.{u} Γ X (M.closed (ring.{u} Γ X)) (M.model (ring.{u} Γ X)))

/-- The three normalized presentation transports identify the actual scalar compositors.
The section compositor is scalarHomExtensionComp followed by the coefficient-functor law.
Source: Stacks 07A6, 0D6D
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG steps 5 and 7. Transpose both paths through the actual scalar adjunctions.
The restriction comparisons fix every section, so their composites agree. The unit
normalization of the three extension comparisons identifies their left-adjoint mates.
Uniqueness of left adjoints gives the stated equation. -/
theorem scalarTransport_composition
    {Δ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
    [MonObj Δ] [IsCommMonObj Δ] (b : Γ ⟶ Δ) [IsMonHom b]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} b Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap.{u} (a ≫ b) Z))]
    (PΔ : HomPresentation.{u} Δ X (M.closed (ring.{u} Δ X)) (M.model (ring.{u} Δ X)))
    (ta : ScalarTransport.{u} (a := a) (X := X) (M := M) (μ := μ)
      (PΛ := PΛ) (PΓ := PΓ))
    (tb : ScalarTransport.{u} (a := b) (X := X) (M := M) (μ := μ)
      (PΛ := PΓ) (PΓ := PΔ))
    (tab : ScalarTransport.{u} (a := a ≫ b) (X := X) (M := M) (μ := μ)
      (PΛ := PΛ) (PΓ := PΔ))
    (K : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    (forward.{u} Δ X).map ((internalExtensionComp.{u} (X := X) a b).hom.app K) ≫
        tab.extension.hom.app K =
      tb.extension.hom.app ((CondensedRing.internalScalarExtension.{u} a X).obj K) ≫
        (M.scalar (sectionCoefficientMap.{u} b)).derived.map (ta.extension.hom.app K) ≫
        (sectionExtensionComp.{u} a M b).hom.app ((forward.{u} Λ X).obj K) := by
  sorry

/-- The five-bijection restricted maps are identified with their evaluation normalization.
Source: Stacks 07A6, 08J9
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 8. The Hom evaluation equation, scalar tensor equation and
normalized scalar adjunction identify each of the five Hom bijections.
Their values at the identity agree, giving the stated equality of maps. On the
section side the value at the identity is that of the recorded five-bijection
composite scalarHomBijection (def-sfb-scalar-hom-comparison-data); it is the
component of the comparison of lem-sfb-closed-scalar-hom-comparison. -/
theorem restricted_hom_transport
    (t : ScalarTransport.{u} (a := a) (X := X) (M := M) (μ := μ) (PΛ := PΛ) (PΓ := PΓ))
    (K : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (N : DerivedCategory.{u + 1} (Internal.{u} Γ X)) :
    (forward.{u} Λ X).map (internalRestrictedHom.{u} a K N) ≫
        PΛ.homIso.hom.app
          (op K, (Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory.obj N) ≫
        (hom.{u} Λ X).map
          (X := (op ((forward.{u} Λ X).obj K), (forward.{u} Λ X).obj
            ((Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory.obj N)))
          (Y := (op ((forward.{u} Λ X).obj K),
            (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
              (sectionCoefficientMap.{u} a)).obj ((forward.{u} Γ X).obj N)))
          (𝟙 _, t.derivedRestriction.hom.app N) =
      t.derivedRestriction.hom.app
          (((CondensedRing.derivedHom.{u} Γ X).obj
            (op ((CondensedRing.internalScalarExtension.{u} a X).obj K))).obj N) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionCoefficientMap.{u} a)).map
          (PΓ.homIso.hom.app
              (op ((CondensedRing.internalScalarExtension.{u} a X).obj K), N) ≫
            (hom.{u} Γ X).map
              (X := (op ((forward.{u} Γ X).obj
                ((CondensedRing.internalScalarExtension.{u} a X).obj K)),
                (forward.{u} Γ X).obj N))
              (Y := (op ((M.scalar (sectionCoefficientMap.{u} a)).derived.obj
                ((forward.{u} Λ X).obj K)), (forward.{u} Γ X).obj N))
              ((t.extension.inv.app K).op, 𝟙 _)) ≫
        scalarHomBijection M (sectionCoefficientMap.{u} a) (μ (sectionCoefficientMap.{u} a))
          ((scalarHomSource M (sectionCoefficientMap.{u} a)).obj
            (op ((forward.{u} Λ X).obj K), (forward.{u} Γ X).obj N))
          ((forward.{u} Λ X).obj K) ((forward.{u} Γ X).obj N) (𝟙 _) := by
  sorry

/-- The normalized comparison identifies both scalar Hom maps and scalar adjunctions.
Source: Stacks 03EK, 07A4, 07A6, 08J9, 0A95
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 5 applies internal_section_scalar_adjunction. Its unchanged section
maps identify restrictions; its normalized adjunction gives the extension comparison.
The internal and section tensorators have the same balanced-generator formula, so
are equal on ordinary tensors, then on flat-term K-flat total representatives, then
on all derived objects. For step 6, transpose both scalar Hom maps: the first map
is inverse tensor comparison followed by scalar-extended evaluation. The normalized
tensor square and Hom evaluation square identify these transposes, hence the maps.
Step 7 is stated separately by internalScalarHom_composition and
internalScalarHom_identity, and by the normalized extension transport equations.
Naturality includes arbitrary derived morphisms. Step 8 transports the five closed
and scalar Hom bijections: the same transposes, scalar units and tensor comparisons
occur, so their evaluation-normalized restricted comparisons agree as well.
No boundedness, perfectness, continuity or invertibility of the Hom map is used. -/
theorem internal_section_hom_continuity_comparison :
    Nonempty (ScalarTransport.{u} (a := a) (X := X) (M := M) (μ := μ)
      (PΛ := PΛ) (PΓ := PΓ)) := by
  sorry

end Scalar

section IdentityTransport
attribute [local semireducible] Functor.mapDerivedCategory sectionModuleEquivalence

/-- The normalized identity transport identifies the internal and section scalar unitors.
The latter is scalarHomExtensionId with the actual coefficient-functor identity law.
Source: Stacks 07A6
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 7. The scalar identity restriction fixes every section. Transpose
the two maps through the identity scalar adjunction, using the adjunction field of
the transport. Both are its identity unit, so injectivity gives equality. -/
theorem scalarTransport_identity
    (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
    (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S),
      ScalarHomTensorComparison.{u + 1, u, u, u + 1} M f)
    (P : HomPresentation.{u} Λ X (M.closed (ring.{u} Λ X)) (M.model (ring.{u} Λ X)))
    (t : ScalarTransport.{u} (a := 𝟙 Λ) (X := X) (M := M) (μ := μ) (PΛ := P) (PΓ := P))
    (K : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    (forward.{u} Λ X).map ((internalExtensionId.{u} Λ X).hom.app K) =
      t.extension.hom.app K ≫
        (sectionExtensionId.{u} Λ X M).hom.app ((forward.{u} Λ X).obj K) := by
  unfold internalExtensionId internalRestrictionId sectionExtensionId forward
  exact ringed_identity_transport (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X)
    _ (coefficientMap_id (Λ := Λ) X) _
    ((sectionCoefficientFunctor.{u} X).map_id (CommMon.mk Λ)) M
    (internalScalarAdjunction.{u} Λ X (𝟙 Λ)) t.restriction t.sections
    t.derivedRestriction t.extension t.restrictionNormalization (by
      intro A B f
      unfold internalScalarAdjunction
      exact t.adjunction A B f) K


end IdentityTransport


attribute [local irreducible] forward complexForward
  CondensedRing.internalScalarExtension CondensedRing.internalScalarTensorIso
  CategoryTheory.Mod.comap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation and all transition squares of an actual filtered coefficient diagram,
including its induced map on exact termwise colimits. The representative map f is
pinned at each object to the restricted native scalar evaluation; it is not an
arbitrary pair of unrelated colimit maps. The entire representative functors,
including their transition arrows, are transported by complexForward.
Source: Stacks 08J9, 0A95, 03DB; Categories 002F
(blueprint: lem-sfb-internal-section-hom-continuity-comparison).
Proof: DAG step 9. Apply the normalized scalar Hom equality at each coefficient
object and the restriction comparison, obtaining the first equation. The arrow
squares follow from naturality of the same representative transformation, with
composition normalized by scalarTransport_composition. Transport the whole two
functors and that transformation. The degreewise colimit universal property,
checked on every leg, gives the last equation. Exact filtered colimits preserve
quasi-isomorphisms. No invertibility of an evaluation or continuity is asserted. -/
theorem coefficient_diagram_evaluation_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (C : I ⥤ Under (CommMon.mk Λ))
    [∀ (i : I) (Z : Scheme.{u}), PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap.{u} (C.obj i).hom.hom.hom Z))]
    (exactArrows : ∀ (i j : I) (f : i ⟶ j) (Z : Scheme.{u}), PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap.{u} (C.map f).right.hom.hom Z)))
    (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
    (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S),
      ScalarHomTensorComparison.{u + 1, u, u, u + 1} M a)
    (P : HomPresentation.{u} Λ X (M.closed (ring.{u} Λ X)) (M.model (ring.{u} Λ X)))
    (Pi : ∀ i : I, HomPresentation.{u} (C.obj i).right.X X
      (M.closed (ring.{u} (C.obj i).right.X X)) (M.model (ring.{u} (C.obj i).right.X X)))
    (t : ∀ i : I, ScalarTransport.{u} (a := (C.obj i).hom.hom.hom) (X := X)
      (M := M) (μ := μ) (PΛ := P) (PΓ := Pi i))
    (K L : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (D E : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ) (f : D ⟶ E)
    (s : ∀ i : I, DerivedCategory.Q.obj (D.obj i) ≅
      (Mod.comap (coefficientMap.{u} (C.obj i).hom.hom.hom X)).mapDerivedCategory.obj
        ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj
          (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L)))
    (r : ∀ i : I, DerivedCategory.Q.obj (E.obj i) ≅
      (Mod.comap (coefficientMap.{u} (C.obj i).hom.hom.hom X)).mapDerivedCategory.obj
        (((CondensedRing.derivedHom.{u} (C.obj i).right.X X).obj
          (op ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj K))).obj
            ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj L)))
    (_normalization : ∀ i : I, DerivedCategory.Q.map (f.app i) ≫ (r i).hom =
      (s i).hom ≫
        (Mod.comap (coefficientMap.{u} (C.obj i).hom.hom.hom X)).mapDerivedCategory.map
          (internalScalarHom.{u} (C.obj i).hom.hom.hom K L)) :
    (∀ i : I,
      (forward.{u} (C.obj i).right.X X).map
          (internalScalarHom.{u} (C.obj i).hom.hom.hom K L) ≫
        (Pi i).homIso.hom.app
          (op ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj K),
            (CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj L) ≫
        (hom.{u} (C.obj i).right.X X).map
          (X := (op ((forward.{u} (C.obj i).right.X X).obj
              ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj K)),
            (forward.{u} (C.obj i).right.X X).obj
              ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj L)))
          (Y := (op ((M.scalar (sectionCoefficientMap.{u} (C.obj i).hom.hom.hom)).derived.obj
              ((forward.{u} Λ X).obj K)),
            (M.scalar (sectionCoefficientMap.{u} (C.obj i).hom.hom.hom)).derived.obj
              ((forward.{u} Λ X).obj L)))
          (((t i).extension.inv.app K).op, (t i).extension.hom.app L) =
        (t i).extension.hom.app (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
          (M.scalar (sectionCoefficientMap.{u} (C.obj i).hom.hom.hom)).derived.map
            (P.homIso.hom.app (op K, L)) ≫
          coefficientBaseChangeHom (M.closed (ring.{u} Λ X))
            (M.closed (ring.{u} (C.obj i).right.X X))
            (M.scalar (sectionCoefficientMap.{u} (C.obj i).hom.hom.hom)).derived
            (μ (sectionCoefficientMap.{u} (C.obj i).hom.hom.hom)).iso
            ((forward.{u} Λ X).obj K) ((forward.{u} Λ X).obj L)) ∧
    (∀ (i j : I) (h : i ⟶ j),
      letI : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap.{u} (C.map h).right.hom.hom Z)) :=
          exactArrows i j h
      letI : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap.{u}
          ((C.obj i).hom.hom.hom ≫ (C.map h).right.hom.hom) Z)) :=
            internalScalarComposite_exact Λ (C.obj i).hom.hom.hom (C.map h).right.hom.hom
      (C.obj i).hom.hom.hom ≫ (C.map h).right.hom.hom = (C.obj j).hom.hom.hom ∧
      (CondensedRing.internalScalarExtension.{u} (C.map h).right.hom.hom X).map
          (internalScalarHom.{u} (C.obj i).hom.hom.hom K L) ≫
        internalScalarHom.{u} (C.map h).right.hom.hom
          ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj K)
          ((CondensedRing.internalScalarExtension.{u} (C.obj i).hom.hom.hom X).obj L) ≫
        (Functor.uncurry.obj (CondensedRing.derivedHom.{u} (C.obj j).right.X X)).map
          (Prod.mkHom
            ((internalExtensionComp.{u} (X := X)
              (C.obj i).hom.hom.hom (C.map h).right.hom.hom).inv.app K).op
            ((internalExtensionComp.{u} (X := X)
              (C.obj i).hom.hom.hom (C.map h).right.hom.hom).hom.app L)) =
        (internalExtensionComp.{u} (X := X)
          (C.obj i).hom.hom.hom (C.map h).right.hom.hom).hom.app
            (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
          internalScalarHom.{u} ((C.obj i).hom.hom.hom ≫ (C.map h).right.hom.hom) K L) ∧
    (∀ (i j : I) (h : i ⟶ j),
      (complexForward.{u} Λ X).map (D.map h) ≫ (complexForward.{u} Λ X).map (f.app j) =
        (complexForward.{u} Λ X).map (f.app i) ≫ (complexForward.{u} Λ X).map (E.map h)) ∧
    (complexForward.{u} Λ X).map (colimMap f) ≫
        (preservesColimitIso (complexForward.{u} Λ X) E).hom =
      (preservesColimitIso (complexForward.{u} Λ X) D).hom ≫
        colimMap (Functor.whiskerRight f (complexForward.{u} Λ X)) := by
  refine ⟨fun i ↦ (t i).hom K L, ?_, ?_, ?_⟩
  · intro i j h
    have : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap.{u} (C.map h).right.hom.hom Z)) :=
      exactArrows i j h
    have : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap.{u}
          ((C.obj i).hom.hom.hom ≫ (C.map h).right.hom.hom) Z)) :=
      internalScalarComposite_exact Λ (C.obj i).hom.hom.hom (C.map h).right.hom.hom
    refine ⟨?_, internalScalarHom_composition (C.obj i).hom.hom.hom
      (C.map h).right.hom.hom K L⟩
    exact congrArg (fun f ↦ f.hom.hom) (Under.w (C.map h))
  · intro i j h
    simpa only [← Functor.map_comp] using
      congrArg (complexForward.{u} Λ X).map (f.naturality h)
  · exact (preservesColimitNatIso (complexForward.{u} Λ X)).hom.naturality f

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
