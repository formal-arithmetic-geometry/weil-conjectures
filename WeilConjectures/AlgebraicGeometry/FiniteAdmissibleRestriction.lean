/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.LocalizingClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteComparisonFaithful
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentationSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentationSupport
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModelSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.Flat
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodedPresentation
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import all WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleGeneration

/-! # Finite admissible comparison restriction helper

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-prop-ctf-finite-comparison`, statement and proof
(blueprint: new-ctf-finite-admissible-restriction).

We restrict the fully faithful ordinary-module comparison with coefficients `ULift A`
to the localizing closures. The Noetherian finite-Tor comparison is transported from
coefficient-sized models through the existing realization equivalences. The source
generation theorem then identifies the restricted source with the entire etale category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

-- The following private closure argument is the scalar-independent argument in
-- WeilConjectures.AlgebraicGeometry.FiniteComparisonLocalizing. Keeping it local avoids importing that
-- module's scalar-specific coefficient constructions and field restrictions.
section LocalizingArgument
universe w v₁ v₂
namespace CategoryTheory

variable {C : Type w} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem closureLocalizing (S : ObjectProperty C) :
    IsLocalizingSubcategory (localizingClosure S) := by
  have hiso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  let := hiso
  have hzero : (localizingClosure S).ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hzero
  have hshift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    rw [ObjectProperty.prop_shift_iff]
    intro P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)
  let := hshift
  have htri : (localizingClosure S).IsTriangulated := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    apply ObjectProperty.le_isoClosure
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS)
  refine ⟨htri, hiso, ?_⟩
  intro I F hF hK
  change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → _
  intro P hP hS
  exact hP.2.2 F hF (fun i ↦ hK i P hP hS)

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.2.2 (G ⋙ F) inferInstance hPG)

private theorem imageLocalizing (P : ObjectProperty C) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [Coreflective F] (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.map F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I H hH hPH
  let := hH
  have hHF (j : Discrete I) : F.essImage (H.obj j) := by
    obtain ⟨K, _, e⟩ := hPH j.as
    exact ⟨K, e⟩
  let G := Functor.essImage.liftFunctor H F hHF
  let e := Functor.essImage.liftFunctorCompIso H F hHF
  let : HasColimit (G ⋙ F) := hasColimit_of_iso e
  let : HasColimit G := hasColimit_of_coreflective G F
  have hPG (i : I) : P (G.obj (Discrete.mk i)) := by
    obtain ⟨K, hK, ⟨iK⟩⟩ := hPH i
    exact P.prop_of_iso (F.preimageIso (iK ≪≫ (e.app (Discrete.mk i)).symm)) hK
  refine ⟨colimit G, hP.2.2 G inferInstance hPG, ⟨?_⟩⟩
  exact (preservesColimitIso F G) ≪≫ HasColimit.isoOfNatIso e


private theorem closureEquivalence (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [Coreflective F]
    (hS : ∀ K, S K → localizingClosure T (F.obj K))
    (hT : ∀ K, T K → (localizingClosure S).map F K) :
    ∃ hpres : ∀ K, localizingClosure S K → localizingClosure T (F.obj K),
      ((localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence := by
  have hpres (K : C) (hK : localizingClosure S K) :
      localizingClosure T (F.obj K) := by
    exact hK ((localizingClosure T).inverseImage F)
      (inverseImageLocalizing _ _ (closureLocalizing T)) hS
  refine ⟨hpres, ?_⟩
  let H := (localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  have himage (K : D) (hK : localizingClosure T K) :
      (localizingClosure S).map F K :=
    hK _ (imageLocalizing _ F (closureLocalizing S)) hT
  have : H.EssSurj := by
    constructor
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := himage K.obj K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact { }

end CategoryTheory
end LocalizingArgument

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  CategoryTheory.moduleMonoidal CategoryTheory.moduleSymmetric
  CategoryTheory.moduleClosed CategoryTheory.modulePreadditive CategoryTheory.moduleGrothendieck
  CategoryTheory.flatResolution CategoryTheory.standardDerived

/-- The finite-coefficient comparison identifies the entire etale derived category
with the localizing closure of pro-etale constructible finite-Tor objects.

Source: blueprint `sk-prop-ctf-finite-comparison`, proof steps 1--3 and 6
(blueprint: new-ctf-finite-admissible-restriction).

Proof: identify the two etale constructibility predicates using the equivalence
between finite-valued and finite-stalk constructible sheaves. The Noetherian finite-Tor
comparison, transported through the coefficient-model realization equivalences,
identifies the finite-Tor generator predicates. The unbounded comparison is exact,
fully faithful, and preserves coproducts. Its inverse image of the target closure
is localizing and contains the source generators. Its essential image on the
source closure is also localizing: fullness lifts arrows, exactness identifies
cones, and preservation of sums identifies coproducts. Minimality of both closures
therefore gives an equivalence of closures. The generation helper identifies the
source closure with the entire etale category. The restricted functor is the
original comparison followed by the subtype factorization, giving the stated
natural identification after inclusion. -/
theorem finiteAdmissibleRestriction
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type u) [CommRing A] [Finite A] (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    (∃ E : Etale.DerivedCategoryModule (ULift.{u + 1} A) X ≌
        (CategoryTheory.localizingClosure
          (DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).FullSubcategory,
      Nonempty (E.functor ⋙ (CategoryTheory.localizingClosure
          (DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).ι ≅
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory)) := by
  classical
  let R := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} R
  let F := (comparisonUpperStar C X).mapDerivedCategory
  let S := Etale.DerivedCategory.isBoundedConstructible R X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let T := DerivedCategory.constructibleFiniteTor C X
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have hnil : ∃ n : ℕ, (ℓ : R) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, (ULift.ringEquiv : R ≃+* A).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero] using hn
  have hbc (K : Etale.DerivedCategoryModule R X) :
      Etale.DerivedCategory.isBoundedConstructible R X K ↔
        Etale.DerivedCategory.boundedConstructible C X K := by
    constructor
    · rintro ⟨hc, a, b, hab, hz⟩
      refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, ?_⟩
      · exact (_root_.DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ hz q (.inl hq))
      · exact (_root_.DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ hz q (.inr hq))
      · intro q
        exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc q)
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
      refine ⟨fun q ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc q),
        min a b, b, min_le_right _ _, ?_⟩
      intro q hq
      rcases hq with hq | hq
      · exact (_root_.DerivedCategory.isGE_iff K a).mp ha q
          (lt_of_lt_of_le hq (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff K b).mp hb q hq
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) R)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) R)) :=
    HasDerivedCategory.standard _
  let E := (finiteComparisonEtaleModelRealization X R).mapDerivedCategory
  let G := (finiteComparisonProEtaleModelRealization X R).mapDerivedCategory
  obtain ⟨D, hD, hmodel, _, _⟩ := finiteTorComparisonNoetherian.{u, u + 1} X R
  obtain ⟨esquare⟩ := finiteComparisonModelDerivedSquare X R D hD
  have hpro (M : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) R)) :
      (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ M a b) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (G.obj M) := by
    rw [FiniteComparisonPresentationSupport.coefficient_finite_native]
    let H := finiteComparisonProEtaleModelRealization X R
    let : H.Monoidal := proRealization_monoidal X R
    let := H.preservesFlat_of_isEquivalence
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    exact (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff H a b M).symm
  let : (Etale.DerivedCategory.isBoundedConstructible R X).IsClosedUnderIsomorphisms :=
    etale_bounded_iso X R
  have htor (K : Etale.DerivedCategoryModule R X)
      (hc : Etale.DerivedCategory.isBoundedConstructible R X K) :
      _root_.DerivedCategory.finiteTorAmplitude _ K ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (F.obj K) := by
    obtain ⟨M, ⟨eM⟩⟩ := Functor.EssSurj.mem_essImage E K
    have hcM := (coefficient_etale_bounded X R M).mpr
      ((Etale.DerivedCategory.isBoundedConstructible R X).prop_of_iso eM.symm hc)
    have hm : (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ M a b) ↔
        (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ (D.obj M) a b) := by
      constructor
      · rintro ⟨a, b, h⟩
        exact ⟨a, b, (hmodel M hcM a b h.1).mp h⟩
      · rintro ⟨a, b, h⟩
        exact ⟨a, b, (hmodel M hcM a b h.1).mpr h⟩
    have hleft : _root_.DerivedCategory.finiteTorAmplitude _ (E.obj M) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ K :=
      ⟨fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso eM h,
        fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso eM.symm h⟩
    let e : G.obj (D.obj M) ≅ F.obj K := (esquare.app M).symm ≪≫ F.mapIso eM
    have hright : _root_.DerivedCategory.finiteTorAmplitude _ (G.obj (D.obj M)) ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (F.obj K) :=
      ⟨fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h,
        fun h ↦ (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm h⟩
    exact hleft.symm.trans ((coefficient_etale_finiteTor X R M).symm.trans
      (hm.trans ((hpro (D.obj M)).trans hright)))
  obtain ⟨hff⟩ := finiteComparisonOrdinary_fullyFaithful R k hbase hℓ hnil X
  let : F.Full := hff.full
  let : F.Faithful := hff.faithful
  let adj := (comparisonAdjunction C X).mapDerivedCategoryRightDerivedAdjunction
  let : Coreflective F := { R := _, adj := adj }
  obtain ⟨hpres, hequiv⟩ := CategoryTheory.closureEquivalence S T F
    (fun K hK P hP hinc ↦ hinc _
      ⟨⟨K, (hbc K).mp hK.1, ⟨Iso.refl _⟩⟩, (htor K hK.1).mp hK.2⟩)
    (fun K hK ↦ by
      obtain ⟨⟨L, hL, ⟨e⟩⟩, a, b, ht⟩ := hK
      have hc := (hbc L).mpr hL
      have hf : _root_.DerivedCategory.finiteTorAmplitude _ (F.obj L) :=
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm ⟨a, b, ht⟩
      exact ⟨L, fun P hP hinc ↦ hinc _ ⟨hc, (htor L hc).mpr hf⟩, ⟨e⟩⟩)
  let H := (CategoryTheory.localizingClosure T).lift
    ((CategoryTheory.localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  let : H.IsEquivalence := hequiv
  have hall (K : Etale.DerivedCategoryModule R X) :
      CategoryTheory.localizingClosure S K := by
    rw [finiteAdmissibleGeneration k hbase ℓ hℓ A hA X]
    trivial
  let L := (CategoryTheory.localizingClosure S).lift (𝟭 _) hall
  let : L.EssSurj := ⟨fun K ↦ ⟨K.obj, ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩⟩
  let : L.IsEquivalence := { }
  let E := L.asEquivalence.trans H.asEquivalence
  exact ⟨E, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale
