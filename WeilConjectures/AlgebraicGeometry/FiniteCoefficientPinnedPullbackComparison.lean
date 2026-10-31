/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHeartPullback
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHeartEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHeartTensor
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPullbackEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientTensorPullbackEncoding
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOperationEncoding
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHeartPullbackComposition
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
import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
import WeilConjectures.CategoryTheory.DerivedCategory.ExactDerivedTensorSquare
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.CategoryTheory.DerivedTensorRightExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-! # The specified finite-coefficient inverse-image comparison

Source: blueprint sec-smooth-purity, sk-prop-sp-purity-bc, opening finite-ring paragraph;
agent-written pinning of its coefficient comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).

The comparison is the localization of the normalized heart mate, conjugated by the
canonical exact/total-derived comparisons. No existential pullback comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- Identification of the concrete section-action heart with the Encoding heart.
Source: the two Encoding normalization equations, clause (1)
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedHeartIdentification (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    heart A R e T E ≅ coefficientHeartEncoding A e T E :=
  eqToIso (heart_eq A R e T E)

/-- The specified heart mate expressed using the Encoding heart functors.
Source: clause (1), transporting heartPull along the Encoding identifications
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedHeartPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.upperStar R f ⋙ coefficientHeartEncoding A e X EX ≅
      coefficientHeartEncoding A e Y EY ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f :=
  isoWhiskerLeft _ (pinnedHeartIdentification A R e X EX).symm ≪≫
    heartPull A R e f EX EY ≪≫
    isoWhiskerRight (pinnedHeartIdentification A R e Y EY) _

/-- The inverse normalized heart mate is the published left-adjoint uniqueness comparison.
Source: clause (1) of the finite-ring comparison pinning
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).
Proof: both direct-image comparisons are the identity on additive sections with the same
coefficient-isomorphism factor. Their inverse mates satisfy the same adjunction unit
identity. The injectivity of the adjunction hom-equivalence identifies the mates. -/
theorem pinnedHeartPull_inverse (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    (pinnedHeartPull A R e f EX EY).symm = coefficientHeartPullIso A e f EX EY := by
  sorry

/-- The canonical identification with the unchanged underlying additive sections.
Source: Encoding normalization, clause (2)
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedSectionsIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    coefficientHeartEncoding A e T E ⋙ sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ≅
        Mod.forget (condensedRingObj R T) :=
  eqToIso (by
    unfold coefficientHeartEncoding
    rw [E.ordinary_functor, E.fixed_functor]
    rfl)

/-- Pure-pair normalization of a strong monoidal Encoding heart, on actual local sections.
The section identifications only expose the two Encoding normalization equations.
Source: clause (2), the section-tensor normalization
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def PinnedHeartNormalized (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T)
    (m : (coefficientHeartEncoding A e T E).Monoidal) : Prop :=
  ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T))
    (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((m.toLaxMonoidal.μ M N).hom.app V)
      (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
        ((coefficientHeartEncoding A e T E).obj M)
        ((coefficientHeartEncoding A e T E).obj N) V
        ((((pinnedSectionsIso A R e T E).inv.app M).hom.app V).hom x)
        ((((pinnedSectionsIso A R e T E).inv.app N).hom.app V).hom y)) =
      (((pinnedSectionsIso A R e T E).inv.app (M ⊗ N)).hom.app V).hom
        (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
          (condensedRingObj R T) M N V x y)

/-- Monoidality of the specified heart map for given strong structures on its vertices.
Source: clause (2), using the published geometric pullback structures
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def PinnedHeartMonoidal (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y)
    (mX : (coefficientHeartEncoding A e X EX).Monoidal)
    (mY : (coefficientHeartEncoding A e Y EY).Monoidal) : Prop :=
  letI := mX
  letI := mY
  letI : (CondensedRing.upperStar R f).Monoidal := CondensedRing.monoidal_upperStar R f
  letI : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).Monoidal :=
    ProEtale.monoidal_upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  NatTrans.IsMonoidal (pinnedHeartPull A R e f EX EY).hom

/-- Normalized section-action structures make the specified heart comparison monoidal.
Source: clause (2), the monoidal mate of the identity-on-sections comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).
Proof: the section, scalar-restriction and coefficient-isomorphism tensorators preserve
pure pairs. The direct-image comparison therefore respects tensorators and units. Its
conjugate under the strong monoidal encoding equivalences is monoidal; the geometric
adjunction units and counits are monoidal for the published pullback structures. Their
mate is monoidal as a composite of whiskered monoidal maps. Clause (1) identifies it
with the inverse of the specified heartPull. Inverting gives the required monoidality.
The unit normalization follows from the tensor normalization and the unit coherences.
A normalized structure exists by the section-tensor normalization, transported along the
Encoding equations; it is unique, since local pure pairs generate the sheafified balanced
tensor and a strong tensorator determines its unit, so the monoidality holds for every
normalized pair of structures. -/
theorem pinnedHeart_normalized_monoidal (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) :
    (∀ T : Scheme.{u}, ∃ m : (coefficientHeartEncoding A e T (E T)).Monoidal,
      PinnedHeartNormalized A R e T (E T) m) ∧
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (mX : (coefficientHeartEncoding A e X (E X)).Monoidal)
        (mY : (coefficientHeartEncoding A e Y (E Y)).Monoidal),
        PinnedHeartNormalized A R e X (E X) mX →
        PinnedHeartNormalized A R e Y (E Y) mY →
        PinnedHeartMonoidal A R e f (E X) (E Y) mX mY := by
  sorry

/-- The canonical identification of the localized heart encoding with coefficientEncoding.
Source: clause (3), the termwise composite-functor comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedHeartDerivedIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    (coefficientHeartEncoding A e T E).mapDerivedCategory ≅ coefficientEncoding A e T E :=
  mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom T))
    (E.ordinary.functor ⋙ E.fixed.functor)

/-- The specified comparison: localize the heart mate and use the canonical comparisons
with the total derived inverse images on its two edges.
Source: clause (3), localization of heartPull
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedPullback (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull R f ⋙ coefficientEncoding A e X (E X) ≅
      coefficientEncoding A e Y (E Y) ⋙ fixedPull A f :=
  isoWhiskerRight (CondensedRing.modulePullbackExactComparison R f) _ ≪≫
    isoWhiskerLeft _ (pinnedHeartDerivedIso A R e X (E X)).symm ≪≫
    mapDerivedCategorySquareIso (pinnedHeartPull A R e f (E X) (E Y)) ≪≫
    isoWhiskerRight (pinnedHeartDerivedIso A R e Y (E Y)) _ ≪≫
    isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm

/-- The tensor comparison obtained from a given strong heart structure on K-flat
resolutions, transported along the canonical exact and coefficient-encoding comparisons.
Source: clause (3), derived tensor normalization
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedDerivedTensor (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T)
    (m : (coefficientHeartEncoding A e T E).Monoidal) :
    (postcompose₂.obj (coefficientEncoding A e T E)).obj
      (CondensedRing.derivedTensor R T) ≅
    (((Functor.whiskeringLeft₂ _).obj (coefficientEncoding A e T E)).obj
      (coefficientEncoding A e T E)).obj
        (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T) :=
  letI := m
  letI : (coefficientHeartEncoding A e T E).PreservesFlat :=
    Functor.preservesFlat_of_isEquivalence _
  let d : (coefficientHeartEncoding A e T E).leftDerivedFunctor ≅
      coefficientEncoding A e T E :=
    (coefficientHeartEncoding A e T E).leftDerivedFunctorIsoMapDerivedCategory ≪≫
      pinnedHeartDerivedIso A R e T E
  (postcompose₂.mapIso d.symm).app (CondensedRing.derivedTensor R T) ≪≫
    asIso (coefficientHeartEncoding A e T E).leftDerivedTensorComparison ≪≫
    ((((Functor.whiskeringLeft₂ _).obj
      (coefficientHeartEncoding A e T E).leftDerivedFunctor).mapIso d).app
        (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)) ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso d).app (coefficientEncoding A e T E)).app
      (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)

/-- The tensor-pullback equation for the prescribed comparison and prescribed tensorators.
Source: clause (3), the equation of finite-coefficient tensor/pullback encoding
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).
Proof: all four heart categories have the native closed braided Grothendieck structures,
additive tensors and functorial flat resolutions. The encoding equivalences are exact and
preserve flats, and geometric pullback is exact and preserves flats. Apply the exact-derived
tensor-square theorem to the inverse monoidal heart mate. Its comparison is the localized
mate, hence the inverse of pinnedPullback. On corresponding K-flat resolutions its vertex
tensorators are precisely pinnedDerivedTensor. The native pullback comparisons are the
same universal derived tensor comparisons, by their counit normalization and uniqueness.
Thus all four edges retain their published maps and the compatibility equation follows. -/
theorem pinnedPullback_tensor (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (mX : (coefficientHeartEncoding A e X (E X)).Monoidal)
    (mY : (coefficientHeartEncoding A e Y (E Y)).Monoidal)
    (hX : PinnedHeartNormalized A R e X (E X) mX)
    (hY : PinnedHeartNormalized A R e Y (E Y) mY) :
    Adjunction.ComparisonCompatible (pinnedPullback A R e E f).symm
      (CondensedRing.leftDerivedUpperStarTensor R f)
      (ProEtale.leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
      (pinnedDerivedTensor A R e X (E X) mX)
      (pinnedDerivedTensor A R e Y (E Y) mY) := by
  sorry

/-- The specified family respects the published total-derived pullback compositors.
Source: clause (3), the compositor equation of the pullback-encoding theorem
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).
Proof: apply the heart composition equation degree by degree and localize. The canonical
exact comparisons identify the published compositors with the localizations of the heart
compositors. Conjugation cancels the two intermediate encoding identifications. Faithfulness
of precomposition with localization gives the displayed equation on all derived objects. -/
theorem pinnedPullback_compositor (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R Z))) :
    (coefficientEncoding A e X (E X)).map
        ((CondensedRing.leftDerivedUpperStarComp R f g).hom.app M) ≫
      (pinnedPullback A R e E f).hom.app ((pull R g).obj M) ≫
      (fixedPull A f).map ((pinnedPullback A R e E g).hom.app M) =
    (pinnedPullback A R e E (f ≫ g)).hom.app M ≫
      (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app
          ((coefficientEncoding A e Z (E Z)).obj M) := by
  sorry

/-- The integer-shift condition, with precisely termwise encoding shifts and the canonical
exact-comparison transport on the two total derived pullbacks.
Source: clause (4) and the specified module-derived shifts
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def PinnedPullbackCommShift (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  letI : (coefficientEncoding A e X (E X)).CommShift ℤ :=
    by unfold coefficientEncoding; infer_instance
  letI : (coefficientEncoding A e Y (E Y)).CommShift ℤ :=
    by unfold coefficientEncoding; infer_instance
  letI : (pull R f).CommShift ℤ := CondensedRing.modulePullbackDerivedCommShift R f
  letI : (fixedPull A f).CommShift ℤ := Functor.CommShift.ofIso
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm ℤ
  NatTrans.CommShift (pinnedPullback A R e E f).hom ℤ

/-- All integer shifts commute with the specified localized comparison.
Source: clause (4), termwise encoding shifts and the specified total-pullback shifts
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).
Proof: shifting reindexes the degreewise heart mate and its differential signs identically
on both sides. The localization factors commute with shifts, as do the canonical exact
pullback comparisons. Whiskering and composing these shift-compatible maps gives the claim. -/
theorem pinnedPullback_commShift (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PinnedPullbackCommShift A R e E f := by
  sorry

/-- Degree-zero comparison of the coefficient encoding, induced termwise.
Source: clause (4), exact-functor single-complex comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedEncodingSingleIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    DerivedCategory.singleFunctor _ 0 ⋙ coefficientEncoding A e T E ≅
      coefficientHeartEncoding A e T E ⋙ DerivedCategory.singleFunctor _ 0 :=
  isoWhiskerLeft _ (pinnedHeartDerivedIso A R e T E).symm ≪≫
    (coefficientHeartEncoding A e T E).mapDerivedCategorySingleFunctor 0

/-- The canonical degree-zero identification on the source of the specified comparison.
Source: clause (4), total/exact comparison and termwise single-complex identifications
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedSingleSourceIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :
    (coefficientEncoding A e X (E X)).obj
      ((pull R f).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      ((coefficientHeartEncoding A e X (E X)).obj ((CondensedRing.upperStar R f).obj M)) :=
  (isoWhiskerRight (CondensedRing.modulePullbackExactComparison R f)
    (coefficientEncoding A e X (E X))).app _ ≪≫
    (coefficientEncoding A e X (E X)).mapIso
      (((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).app M) ≪≫
    (pinnedEncodingSingleIso A R e X (E X)).app ((CondensedRing.upperStar R f).obj M)

/-- The canonical degree-zero identification on the target of the specified comparison.
Source: clause (4), exact ordinary pullback and termwise single-complex identifications
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedSingleTargetIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :
    (fixedPull A f).obj
      ((coefficientEncoding A e Y (E Y)).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
        ((coefficientHeartEncoding A e Y (E Y)).obj M)) :=
  (fixedPull A f).mapIso ((pinnedEncodingSingleIso A R e Y (E Y)).app M) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategorySingleFunctor
      0).app ((coefficientHeartEncoding A e Y (E Y)).obj M)

/-- On degree-zero complexes the specified derived comparison is the heart mate.
Source: clause (4), degree-zero normalization
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).
Proof: on a single complex the sole nonzero component of the termwise mate is the heart
mate at M. The exact-functor single-complex comparisons identify this component with its
localized image. Substituting the defining exact/total-derived and encoding factors of
pinnedPullback gives precisely the two single-complex identifications displayed here. -/
theorem pinnedPullback_single (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :
    (pinnedPullback A R e E f).hom.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (pinnedSingleTargetIso A R e E f M).hom =
      (pinnedSingleSourceIso A R e E f M).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((pinnedHeartPull A R e f (E X) (E Y)).hom.app M) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
