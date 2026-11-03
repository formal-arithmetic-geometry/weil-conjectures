/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralUnderived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentLisse
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Topology.Defs.Filter
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import Mathlib.Data.Set.Finite.Lattice
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLocallyClosedScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetProperHeartBoundFiltration
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Mathlib.AlgebraicGeometry.Fiber
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.Topology.KrullDimension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.IntegralCoefficientQuotientLimit
import all WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundTorsion
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LatticeSupportedHomFiniteComparison
import all WeilConjectures.SixFunctors.IntegralDualTorsionHeartSections
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import all WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
import all WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import all WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.HeartSections.ProperHeartSectionComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WeakContractibleEquivalences
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # The rational constructible proper direct-image bound

Source: literature/blueprint/latest/blueprint/
part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-proper-direct-image-of-unbounded-complexes/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-rational.md and its proof
(blueprint: det-proper-heart-bound-rational).

The finite-subextension and algebraic-closure alternatives are stated separately.
Both use the canonical total right derived functor of the module-object pushforward composite
`CondensedRing.moduleObjectDerivedPushforward`; no abelian-sheaf replacement is introduced.
The coefficient objects are the existing pulled-back condensed rings, and the constructibility
predicate is the existing finite-constant-model predicate. A negative integer fibre bound means
bottom Krull dimension, retaining empty schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

private instance coefficient_module_grothendieck (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} R) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _

private theorem locally_closed_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S Sbar : Scheme.{u}}
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    ((CondensedRing.lowerStar Λ i).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj L)).X =
      (ProEtale.lowerStar Ab.{u + 1} i).obj
        ((ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj L.X) := rfl

attribute [local irreducible] CondensedRing.upperStar upperStarFromPoint
  Mod.monoidalClosed DerivedCategory.monoidalClosed Functor.rightDerivedFunctor

private noncomputable def restriction_section_iso {X : Scheme.{u}} (W : X.ProEt)
    (N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (n : ℕ) :
    ((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) W).rightDerived n).obj N ≅
      ((Sheaf.Γ (Scheme.ProEt.topology W.left) Ab.{u + 1}).rightDerived n).obj
        ((ProEtale.upperStar Ab.{u + 1} W.hom).obj N) := by
  let T := Scheme.ProEt.mk (𝟙 W.left)
  let F := ProEtale.localizationRestriction Ab.{u + 1} W.hom W.prop
  let G := Sheaf.sectionsFunctorAt (Scheme.ProEt.topology W.left) T
  let H := Sheaf.Γ (Scheme.ProEt.topology W.left) Ab.{u + 1}
  have : F.Additive := ⟨by intros; rfl⟩
  have : (MorphismProperty.Over.map ⊤ W.prop).IsContinuous
      (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap W.prop
  have : F.IsLeftAdjoint :=
    (ProEtale.localizationRestrictionLowerStarAdjunction Ab.{u + 1} W.hom W.prop).isLeftAdjoint
  have : F.IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.map ⊤ W.prop) Ab.{u + 1}
        (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology X)).isRightAdjoint
  let W' := (MorphismProperty.Over.map ⊤ W.prop).obj T
  let w : W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp W.hom).symm
  let a : F ⋙ G ≅ Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) W :=
    NatIso.ofComponents (fun M ↦ M.obj.mapIso w.symm.op) (by
      intro M M' f
      exact (f.hom.naturality w.inv.op).symm)
  let b : G ≅ H :=
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId W.left)).symm
  let c := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} W.hom W.prop
  exact (Functor.rightDerivedObjIsoOfIso a n N).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (Functor.isoWhiskerLeft F b) n N ≪≫
    Functor.compRightDerivedObjIso F H
      (fun I _ ↦ H.rightAcyclic_of_injective (F.obj I)) n N ≪≫
    (H.rightDerived n).mapIso (c.app N).symm

private theorem push_zero_of_section_cohomology
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ)
    (hN : ∀ (V : Y.ProEt), IsAffine V.left →
      (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V →
      IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X)
        ((HeartSections.baseChange p).obj V)).rightDerived n).obj N.X)) :
    IsZero ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj
      ((moduleObjectDerivedPushforward Λ p).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  let : HasDerivedCategory.{u + 2} (X.ProEtᵒᵖ ⥤ Ab.{u + 1}) :=
    HasDerivedCategory.standard _
  let P := (DerivedCategory.homologyFunctor _ (n : ℤ)).obj
    ((moduleObjectDerivedPushforward Λ p).obj
      ((DerivedCategory.singleFunctor _ 0).obj N))
  let A := HeartSections.condensedCoefficients Λ X
  let R := HeartSections.ringSheaf (HeartSections.condensedCoefficients Λ Y)
  let E := HeartSections.realization Λ Y
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} R) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  let M := E.functor.obj P
  obtain ⟨e, _, _⟩ := HeartSections.condensedProperHeartSectionComparison Λ p
  obtain ⟨a, _, _⟩ := HeartSections.moduleAbelianSectionComparison A
  have hz (V : Y.ProEt) (ha : IsAffine V.left)
      (hw : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V) :
      IsZero ((HeartSections.sectionsAt (HeartSections.condensedCoefficients Λ Y) V).obj M) := by
    let V' : HeartSections.Tests Y := ⟨V, ha, hw⟩
    let W := (HeartSections.baseChange p).obj V
    let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
    let G := (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op W)
    let b := Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      F N.X n
    let c := Functor.rightDerivedCompObjIso F G n N.X
    have hb : IsZero (((HeartSections.derivedAbelianSectionsPresheaf X (n : ℤ)).obj
        N.X).obj (Opposite.op W)) := by
      exact (hN V ha hw).of_iso (G.mapIso b ≪≫ c.symm)
    have hc := hb.of_iso
      ((evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op W) |>.mapIso
        ((a (n : ℤ)).app ((HeartSections.realization Λ X).functor.obj N)))
    exact hc.of_iso (((e (n : ℤ)).app N).app (Opposite.op V'))
  have hi : IsIso (0 : M ⟶ 0) := by
    apply ((Scheme.ProEt.sections_conservative Y R).2.2.1 M 0 0).2
    intro V ha hw
    have hs : Subsingleton ((SheafOfModules.evaluation R (Opposite.op V)).obj M) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp (hz V ha hw)
    have ht : Subsingleton ((SheafOfModules.evaluation R (Opposite.op V)).obj 0) := by
      exact ModuleCat.isZero_iff_subsingleton.mp
        ((SheafOfModules.evaluation R (Opposite.op V)).map_isZero (isZero_zero _))
    exact ⟨fun _ _ _ ↦ hs.elim _ _, fun y ↦ ⟨0, ht.elim _ _⟩⟩
  have hm : IsZero M := (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))
  exact IsZero.of_full_of_faithful_of_isZero E.functor P hm

private noncomputable def resolution_derived_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    F.rightDerivedFunctorOfQuasiIsoResolutions h ≅ F.rightDerivedFunctor := by
  letI := Functor.IsRightDerivedFunctor.isLeftKanExtension
    F.rightDerivedFunctor F.rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (.up ℤ))
  exact (F.rightDerivedFunctorOfQuasiIsoResolutions_unique h _ F.rightDerivedFunctorUnit
    (fun G ↦ (F.rightDerivedFunctor.homEquivOfIsLeftKanExtension
      F.rightDerivedFunctorUnit G).bijective)).choose

private noncomputable def hypercohomology_single_iso
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (U : X.ProEt) (M : SheafOfModules.{u + 1} R) (n : ℕ) :
    (Scheme.ProEt.ringHypercohomology X R U (n : ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj M) ≅
      ((Scheme.ProEt.hypercoverAbelianEvaluation.{u, u + 1, 0} X R U).rightDerived n).obj M := by
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} R) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  let F := Scheme.ProEt.hypercoverAbelianEvaluation.{u, u + 1, 0} X R U
  have : F.Additive := ⟨by intros; rfl⟩
  let h := Scheme.ProEt.moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X R
  let K := (CochainComplex.singleFunctor (SheafOfModules.{u + 1} R) 0).obj M
  let H := DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ)
  exact (Scheme.ProEt.ringHypercohomologyDerivedIso X R U (n : ℤ)).app K ≪≫
    H.mapIso ((resolution_derived_iso F h).app (DerivedCategory.Q.obj K)) ≪≫
    H.mapIso (F.rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm) ≪≫
    F.homologyRightDerivedFunctorObjSingleFunctorIso M n

private noncomputable def module_section_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ) :
    ((HeartSections.sectionsAt (HeartSections.condensedCoefficients Λ X) U).rightDerived n).obj
        ((HeartSections.realization Λ X).functor.obj M) ≅
      ((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj M.X := by
  letI : HasDerivedCategory.{u + 2} (X.ProEtᵒᵖ ⥤ Ab.{u + 1}) :=
    HasDerivedCategory.standard _
  let A := HeartSections.condensedCoefficients Λ X
  letI : HasDerivedCategory.{u + 1} (HeartSections.Modules A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let N := (HeartSections.realization Λ X).functor.obj M
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let G := (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op U)
  let D := HeartSections.sectionsPresheaf A
  let a := (HeartSections.moduleAbelianSectionComparison A).choose
  let b : HeartSections.moduleCohomologyPresheaf A (n : ℤ) ≅ D.rightDerived n := by
    simpa only [HeartSections.moduleCohomologyPresheaf] using
      D.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n
  let c : F.rightDerived n ≅ HeartSections.derivedAbelianSectionsPresheaf X (n : ℤ) := by
    simpa only [HeartSections.derivedAbelianSectionsPresheaf] using
      (F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).symm
  exact Functor.rightDerivedCompObjIso D G n N ≪≫
    G.mapIso (b.app N).symm ≪≫ G.mapIso ((a (n : ℤ)).app N) ≪≫
    G.mapIso (c.app M.X).symm ≪≫ (Functor.rightDerivedCompObjIso F G n M.X).symm

private theorem section_colimit_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (U : X.ProEt) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (c : Cocone D) (hc : IsColimit c) (n : ℕ)
    (hz : ∀ i, IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      (D.obj i).X)) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj c.pt.X) := by
  let A := HeartSections.condensedCoefficients Λ X
  let R := HeartSections.ringSheaf A
  let E := (HeartSections.realization Λ X).functor
  let K := D ⋙ E ⋙ CochainComplex.singleFunctor _ 0
  let H := Scheme.ProEt.ringHypercohomology X R U (n : ℤ)
  have hb (i : I) (b : ℤ) (h : b < 0) : IsZero ((K.obj i).X b) := by
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have : IsIso (colimit.post K H) :=
    (Scheme.ProEt.boundedContinuity X R K 0 hb).1 U inferInstance inferInstance (n : ℤ)
  have : PreservesColimit K H := preservesColimit_of_isIso_post H K
  have : PreservesColimitsOfShape I (CochainComplex.singleFunctor (SheafOfModules R) 0) := by
    change PreservesColimitsOfShape I (HomologicalComplex.single _ (.up ℤ) 0)
    infer_instance
  have : PreservesColimitsOfShape I E := by
    dsimp only [E]
    infer_instance
  have hK : IsColimit ((E ⋙ CochainComplex.singleFunctor _ 0).mapCocone c) :=
    isColimitOfPreserves _ hc
  have hh := isColimitOfPreserves H hK
  have hzero : IsZero (K ⋙ H) := by
    apply Functor.isZero
    intro i
    exact (hz i).of_iso (hypercohomology_single_iso X R U (E.obj (D.obj i)) n ≪≫
      module_section_iso Λ X U (D.obj i) n)
  have ht := hh.isZero_pt hzero
  exact ht.of_iso (hypercohomology_single_iso X R U (E.obj c.pt) n ≪≫
    module_section_iso Λ X U c.pt n).symm

private theorem lisse_coefficient_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Λ ≅ Λ') [IsMonHom e.hom] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsLisseCoefficientModule Λ' ((Mod.comap (coefficientMap e.inv X)).obj M) := by
  obtain ⟨U, hU⟩ := (isLocallyFree_iff M).mp hM
  refine ⟨U, fun i ↦ ?_⟩
  exact ((hU i).comap (coefficientMap e.inv (U.X i))).of_iso
    ((CondensedRing.comapUpperStarIso e.inv (U.f i)).app M)

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

private theorem section_zero_of_pullback_bound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (V : Y.ProEt)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ)
    (hz : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} (n : ℤ)).obj
      ((Mod.forget (condensedRingObj Λ (pullback p V.hom)) ⋙
        Sheaf.Γ (Scheme.ProEt.topology (pullback p V.hom)) Ab.{u + 1}).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Λ (pullback.fst p V.hom)).obj N))))) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X)
      ((HeartSections.baseChange p).obj V)).rightDerived n).obj N.X) := by
  have ht := hz.of_iso (LatticeBound.compareSections Λ (pullback p V.hom)
    ((CondensedRing.upperStar Λ (pullback.fst p V.hom)).obj N) n).symm
  have hb := ht.of_iso (LatticeBound.upperStar_sections_iso Λ (pullback.fst p V.hom) N n).symm
  let W := (HeartSections.baseChange p).obj V
  let U := Scheme.ProEt.mk (pullback.fst p V.hom)
  have hu := hb.of_iso (restriction_section_iso U N.X n)
  let w : W ≅ U := MorphismProperty.Over.isoMk (pullbackSymmetry V.hom p) (by
    change (pullbackSymmetry V.hom p).hom ≫ pullback.fst p V.hom = pullback.snd V.hom p
    simp)
  let a : Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) W ≅
      Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U :=
    NatIso.ofComponents (fun M ↦ M.obj.mapIso w.symm.op) (by
      intro M M' f
      exact (f.hom.naturality w.inv.op).symm)
  exact hu.of_iso (Functor.rightDerivedObjIsoOfIso a n N.X)

private theorem locally_closed_scalar_restriction_zero
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    {X S Sbar : Scheme.{u}} (j : S ⟶ Sbar) [IsOpenImmersion j]
    (i : Sbar ⟶ X) (U : X.ProEt) (n : ℕ)
    (φ : condensedRingObj Λ' S ⟶ condensedRingObj Λ S) [IsMonHom φ]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (h : IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      (((CondensedRing.lowerStar Λ' i).obj
        ((CondensedRing.openImmersionLowerShriek Λ' j).obj ((Mod.comap φ).obj L))).X))) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      (((CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj L)).X)) := by
  simpa only [locally_closed_underlying, Mod.comap_obj_X] using h

private instance lifted_coefficient_finite (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
  (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional

private noncomputable def integral_presentation_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Profinite.padicIntegersRingObj.{u} ℓ E.val ≅
      DerivedNakayama.integerRing ℓ (ULift.{u} E.val) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
      (integerRingSheafIso ℓ ⟨E.val, E.property⟩)

private instance integral_presentation_monoidal
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsMonHom (integral_presentation_iso.{u} ℓ E).hom := by
  dsimp [integral_presentation_iso]
  infer_instance

attribute [local irreducible] integral_presentation_iso

private theorem lattice_section_bound
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F]
    [Algebra ℚ_[ℓ] F] [FiniteDimensional ℚ_[ℓ] F]
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ F) S))
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ F) L)
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (n : ℕ) (hn : 2 * (d : ℤ) + 1 < (n : ℤ)) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X)
      ((HeartSections.baseChange p).obj V)).rightDerived n).obj
        (((CondensedRing.lowerStar (DerivedNakayama.integerRing ℓ F) i).obj
          ((CondensedRing.openImmersionLowerShriek
            (DerivedNakayama.integerRing ℓ F) j).obj L)).X)) := by
  apply section_zero_of_pullback_bound (DerivedNakayama.integerRing ℓ F) p V _ n
  exact properHeartBoundLattice ℓ F k hchar hell p d hd V hV j i L hL (n : ℤ) hn

private theorem lattice_section_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S))
    (hL : IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S) L)
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (n : ℕ) (hn : 2 * (d : ℤ) + 1 < (n : ℤ)) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X)
      ((HeartSections.baseChange p).obj V)).rightDerived n).obj
        (((CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E.1) i).obj
          ((CondensedRing.openImmersionLowerShriek
            (Profinite.padicIntegersRingObj ℓ E.1) j).obj L)).X)) := by
  apply locally_closed_scalar_restriction_zero _
    (DerivedNakayama.integerRing ℓ (ULift.{u} E.val)) j i
    ((HeartSections.baseChange p).obj V) n
    (coefficientMap (integral_presentation_iso.{u} ℓ E).inv S) L
  exact lattice_section_bound ℓ (ULift.{u} E.val) k hchar hell p d hd j i _
    (lisse_coefficient_transport (integral_presentation_iso.{u} ℓ E) L hL) V hV n hn

private theorem rational_section_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) (U : X.ProEt) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) (n : ℕ)
    (hz : IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      N.X)) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      ((Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).obj N).X) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.1
  let φ := coefficientMap (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) X
  obtain ⟨j, hj, _⟩ := completedCondensedRational.{u} ℓ E
  let D := Functor.ofSequence (fun (_ : ℕ) ↦
    ℓ • 𝟙 (Mod.regular (completedCoefficient X (Profinite.padicIntegersCondensedRing ℓ E)).X))
  let c : Cocone D :=
    { pt := completedRationalModule X ℓ E
      ι := NatTrans.ofSequence (j X) (by
        intro m
        simp only [D,
          Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map,
          Preadditive.nsmul_comp]
        exact (hj X).2.2.1 m) }
  have hlegs (s : Cocone D) (m : ℕ) : ℓ • s.ι.app (m + 1) = s.ι.app m := by
    let b (k : ℕ) :
        Mod.regular (completedCoefficient X (Profinite.padicIntegersCondensedRing ℓ E)).X ⟶
          s.pt := s.ι.app k
    have h : (ℓ • 𝟙 _) ≫ b (m + 1) = b m := by
      simpa only [D, Functor.ofSequence_map_homOfLE_succ] using
        s.w (homOfLE (Nat.le_add_right m 1))
    have h' : ℓ • b (m + 1) = b m := by
      simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
    exact h'
  have hc : IsColimit c := by
    refine ⟨fun s ↦ ((hj X).2.2.2 s.pt (fun m ↦ s.ι.app m) (hlegs s)).choose, ?_, ?_⟩
    · intro s m
      exact ((hj X).2.2.2 s.pt (fun m ↦ s.ι.app m) (hlegs s)).choose_spec.1 m
    · intro s f hf
      exact ((hj X).2.2.2 s.pt (fun m ↦ s.ι.app m) (hlegs s)).choose_spec.2 f hf
  let F := MonoidalCategory.tensorRight N
  let cN := F.mapCocone c
  let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
  have hJ : IsColimit (cN.whisker J) :=
    (Functor.Final.isColimitWhiskerEquiv J cN).symm (isColimitOfPreserves F hc)
  have hstage (m : ULift.{u + 1} ℕ) :
      IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
        (((J ⋙ D ⋙ F).obj m).X)) :=
    hz.of_iso (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).mapIso
      ((Mod.forget (condensedRingObj Λ X)).mapIso (λ_ N)))
  have ht := section_colimit_zero Λ X U (J ⋙ D ⋙ F) (cN.whisker J) hJ n hstage
  exact ht.of_iso (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).mapIso
    (Mod.extendForgetTensorObjIso φ N))

private theorem qlbar_section_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) (U : X.ProEt) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (n : ℕ)
    (hz : IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      N.X)) :
    IsZero (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).obj
      ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N).X) := by
  classical
  let I := ULift.{u + 1} {F : PadicAlgCl.FiniteIntermediateField ℓ // E ≤ F}
  have : Nonempty I := ⟨⟨⟨E, le_rfl⟩⟩⟩
  have : IsDirectedOrder I := ⟨by
    intro F G
    obtain ⟨H, hF, hG⟩ := exists_ge_ge F.down.val G.down.val
    exact ⟨⟨⟨H, F.down.property.trans hF⟩⟩, hF, hG⟩⟩
  let inc : I → PadicAlgCl.FiniteIntermediateField ℓ := fun F ↦ F.down.val
  have hinc : Monotone inc := fun _ _ h ↦ h
  have : hinc.functor.Final := (hinc.final_functor_iff).2 (by
    intro F
    obtain ⟨G, hE, hF⟩ := exists_ge_ge E F
    exact ⟨⟨⟨G, hE⟩⟩, hF⟩)
  let R := padicSubfieldRingObj X ℓ E
  let D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R :=
    { obj := fun F ↦ (Mod.comap (padicSubfieldRingObjMap X ℓ F.down.property)).obj
        (Mod.regular (padicSubfieldRingObj X ℓ F.down.val))
      map := fun {F G} h ↦ tailRestrictedMap _ _
        (padicSubfieldRingObjMap X ℓ (leOfHom (hinc.functor.map h))) (by
          change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _ = _
          rw [← Functor.map_comp]
          rfl)
      map_id := by
        intro F
        ext U x
        change (padicSubfieldRingObjMap X ℓ (le_refl F.down.val)).hom.app U x = x
        change ((upperStarFromPoint X).map (𝟙 _)).hom.app U x = x
        simp
      map_comp := by
        intro F G H a b
        ext U x
        exact congrArg (fun t ↦ t.hom.app U x)
          ((upperStarFromPoint X).map_comp
            (Profinite.padicSubfieldRingObjMap ℓ (leOfHom (hinc.functor.map a)))
            (Profinite.padicSubfieldRingObjMap ℓ (leOfHom (hinc.functor.map b)))) }
  let c : Cocone D :=
    { pt := (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj
        (Mod.regular (padicAlgClRingObj X ℓ))
      ι :=
        { app := fun F ↦ tailRestrictedMap _ _
            (padicSubfieldRingObjToPadicAlgCl X ℓ F.down.val)
            (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.down.property)
          naturality := by
            intro F G h
            ext U x
            exact congrArg (fun t ↦ t.hom.app U x)
              (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom (hinc.functor.map h))) } }
  have hc : IsColimit c := by
    apply isColimitOfReflects (Mod.forget R)
    exact (Functor.Final.isColimitWhiskerEquiv hinc.functor
      (padicAlgClRingObjCocone X ℓ)).symm (isColimitPadicAlgClRingObjCocone X ℓ)
  let T := MonoidalCategory.tensorRight N
  let H := Mod.forget R ⋙ (Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n
  have hstage (F : I) : IsZero (H.obj (T.obj (D.obj F))) := by
    obtain ⟨hb, hf, _⟩ := cartesianCoefficients_finiteFree.{u} ℓ F.down.property
    obtain ⟨e₀, e₁, _⟩ := hf hb.some
    let r := finiteCoefficientDegree ℓ F.down.property
    let e : T.obj (D.obj F) ≅ ⨁ fun _ : Fin r ↦ N :=
      T.mapIso (e₁ X).symm ≪≫ T.mapBiproduct (fun _ : Fin r ↦ Mod.regular R) ≪≫
        biproduct.mapIso (fun _ ↦ λ_ N)
    have hsum : IsZero (⨁ fun _ : Fin r ↦ H.obj N) := by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext
      intro a
      exact hz.eq_of_tgt _ _
    exact hsum.of_iso (H.mapIso e ≪≫ H.mapBiproduct (fun _ : Fin r ↦ N))
  have ht := section_colimit_zero (Profinite.continuousMapRingObj E.1) X U
    (D ⋙ T) (T.mapCocone c) (isColimitOfPreserves T hc) n hstage
  exact ht.of_iso (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) U).rightDerived n).mapIso
    (Mod.extendForgetTensorObjIso (padicSubfieldRingObjToPadicAlgCl X ℓ E) N))

private theorem proper_heart_bound_nonneg
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (Profinite.continuousMapRingObj E.1) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (hM : IsConstantModelConstructible Λ.X X M) (q : ℤ) (hq : 2 * (d : ℤ) + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((moduleObjectDerivedPushforward Λ.X p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let : Fact (ringChar k).Prime :=
    ⟨(CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hchar⟩
  apply det_proper_heart_bound_reduction ℓ (ringChar k) k (Nat.pos_of_ne_zero hchar)
    hell E Λ hΛ p (2 * (d : ℤ) + 1) M hM ?_ ?_ ?_ q hq
  · intro E' _ S Sbar a j i _ _ _ L hL r hr
    lift r to ℕ using (by omega)
    apply push_zero_of_section_cohomology _ p _ r
    intro V ha hV
    have : IsAffine V.left := ha
    exact lattice_section_vanishing ℓ E' k hchar hell p d hd j i L hL V hV r hr
  · intro E' _ S Sbar a j i _ _ _ L hL r hr
    lift r to ℕ using (by omega)
    apply push_zero_of_section_cohomology _ p _ r
    intro V ha hV
    have : IsAffine V.left := ha
    have : CompactSpace V.left := inferInstance
    have : QuasiSeparatedSpace V.left := inferInstance
    let W := (HeartSections.baseChange p).obj V
    have : CompactSpace W.left := by
      have : CompactSpace ((𝟭 Scheme).obj V.left) := by
        change CompactSpace V.left
        infer_instance
      exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom p)
    have : QuasiSeparatedSpace W.left := by
      have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := by
        change QuasiSeparatedSpace V.left
        infer_instance
      exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom p)
    apply rational_section_vanishing ℓ E' X W _ r
    exact lattice_section_vanishing ℓ E' k hchar hell p d hd j i L hL V hV r hr
  · intro E' _ S Sbar a j i _ _ _ L hL r hr
    lift r to ℕ using (by omega)
    apply push_zero_of_section_cohomology _ p _ r
    intro V ha hV
    have : IsAffine V.left := ha
    have : CompactSpace V.left := inferInstance
    have : QuasiSeparatedSpace V.left := inferInstance
    let W := (HeartSections.baseChange p).obj V
    have : CompactSpace W.left := by
      have : CompactSpace ((𝟭 Scheme).obj V.left) := by
        change CompactSpace V.left
        infer_instance
      exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom p)
    have : QuasiSeparatedSpace W.left := by
      have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := by
        change QuasiSeparatedSpace V.left
        infer_instance
      exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom p)
    apply qlbar_section_vanishing ℓ E' X W _ r
    apply rational_section_vanishing ℓ E' X W _ r
    exact lattice_section_vanishing ℓ E' k hchar hell p d hd j i L hL V hV r hr

/-- The proper heart bound for a finite subextension E of Qbar_ell.
Source: latest blueprint
part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-proper-direct-image-of-unbounded-complexes/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-rational.md, finite rational alternative
(blueprint: det-proper-heart-bound-rational).

Proof, following the six steps of the node:
1. If d < 0, all geometric fibres are empty by def-kun-topological-krull-dimension.
   Surjectivity of field-extension spectra (lem-pc-field-extension-surjective) and
   surjective base change (lem-weil-pbc-surjective-base-change) imply X is empty.
   The empty-cover sheaf axiom makes every module and its derived image zero.
2. For d >= 0 apply det-proper-heart-bound-reduction with c = 2d+1. It suffices to
   bound a_!L_0 for every locally closed a and lisse finite free integral lattice
   over every finite coefficient extension, and to check the two scalar passages.
3. By lem-sfb-proper-heart-section-comparison, on affine weakly contractible V over Y
   the sections of R^q p_* N are H^q(X_V,N restricted to X_V). These evaluations
   detect zero by sk-cor-pe-sections. The standing schemes are qcqs over the field;
   lem-weil-pbc-qcqs-over-affine and lem-weil-pbc-qcqs-morphism-permanence give qcqs
   p and X_V. This uses no Noetherian hypothesis on V.
4. Apply det-proper-heart-bound-lattice to a_!L_0 on X_V to get zero for q > 2d+1.
5. By sk-prop-sfb-qlbar-colimit-x and the relative tensor coequalizer of
   sk-def-sfb-change-of-scalars, localization of a_!L_0 is the filtered telescope
   multiplying by ell. Restriction preserves it. Apply sk-cor-pe-bounded-continuity
   to its degree-zero terms, with common lower bound zero, to preserve vanishing.
6. For N = (a_!L_0)[1/ell], finite extensions F containing E are cofinal by composita.
   By sk-prop-sfb-qlbar-colimit-x and sk-def-sfb-change-of-scalars, Qbar_X tensor N
   is the filtered colimit of F_X tensor N. Finite freeness from
   det-prop-sfb-cartesian-coefficients-finite-free makes their underlying abelian
   sheaves finite sums of N. Additivity and sk-cor-pe-bounded-continuity give zero
   cohomology above 2d+1. Section detection and the reduction finish for all M. -/
theorem properHeartBoundRational
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (hM : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  by_cases hn : d < 0
  · let : IsEmpty X := source_empty_of_geometric_fibers_empty p (fun y ↦ by
      simpa only [if_pos hn] using hd y)
    exact (DerivedCategory.singleFunctor _ 0 ⋙
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) p).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q).map_isZero (module_zero_of_empty _ M)
  have hd' (y : Y) : topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d.toNat : WithBot ℕ∞) := by
    simpa only [if_neg hn] using hd y
  exact proper_heart_bound_nonneg ℓ E k hchar hell p d.toNat hd'
    (Mon.mk (Profinite.continuousMapRingObj E.1)) (Or.inl rfl) M hM q (by omega)

/-- The proper heart bound for the finite-subextension-valued condensed ring Qbar_ell.
Source: latest blueprint
part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-proper-direct-image-of-unbounded-complexes/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-rational.md, algebraic-closure alternative
(blueprint: det-proper-heart-bound-rational).

Proof, following the same six node steps:
1. Negative d forces empty geometric fibres and then empty X, by the dimension
   definition, lem-pc-field-extension-surjective and lem-weil-pbc-surjective-base-change.
   The empty-cover sheaf axiom makes the module and its derived pushforward zero.
2. For d >= 0 use det-proper-heart-bound-reduction with c = 2d+1 and initial
   coefficient field Q_ell. Treat every finite extension and locally closed a_!L_0.
3. The formula of lem-sfb-proper-heart-section-comparison identifies evaluations on
   affine weakly contractible V with H^q(X_V,-). These detect zero by sk-cor-pe-sections.
   The qcqs hypotheses follow from lem-weil-pbc-qcqs-over-affine and
   lem-weil-pbc-qcqs-morphism-permanence; V need not be Noetherian.
4. det-proper-heart-bound-lattice gives the lattice cohomology bound q > 2d+1.
5. sk-prop-sfb-qlbar-colimit-x and sk-def-sfb-change-of-scalars identify inversion
   of ell with the multiplication-by-ell filtered telescope of the lattice.
   Restrict to X_V and apply sk-cor-pe-bounded-continuity to degree-zero complexes
   with common lower bound zero. Thus N = (a_!L_0)[1/ell] has the same vanishing.
6. Finite extensions F containing E are cofinal by finite composita. The coefficient
   colimit sk-prop-sfb-qlbar-colimit-x and the relative tensor coequalizer
   sk-def-sfb-change-of-scalars give Qbar_X tensor N as the colimit of F_X tensor N.
   Their underlying abelian sheaves are finite sums of N by
   det-prop-sfb-cartesian-coefficients-finite-free. Additivity and continuity give
   zero cohomology above 2d+1. Section detection and the reduction conclude for M. -/
theorem properHeartBoundRational_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  by_cases hn : d < 0
  · let : IsEmpty X := source_empty_of_geometric_fibers_empty p (fun y ↦ by
      simpa only [if_pos hn] using hd y)
    exact (DerivedCategory.singleFunctor _ 0 ⋙
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q).map_isZero (module_zero_of_empty _ M)
  have hd' (y : Y) : topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d.toNat : WithBot ℕ∞) := by
    simpa only [if_neg hn] using hd y
  let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  exact proper_heart_bound_nonneg ℓ E k hchar hell p d.toNat hd'
    (Mon.mk (Profinite.padicAlgClRingObj ℓ)) (Or.inr rfl) M hM q (by omega)

end AlgebraicGeometry.ProEtale
