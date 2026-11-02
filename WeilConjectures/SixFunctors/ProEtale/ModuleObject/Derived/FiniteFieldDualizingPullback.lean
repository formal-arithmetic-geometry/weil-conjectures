/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.InverseImageModuleFlat
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoverRestrictionConservative
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.SepFinType
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.Compactification.Triangle
import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchangeTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedCoefficientIsoExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.LocalizingIsoLocus
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalSupportMate
import Mathlib.FieldTheory.Separable
import WeilConjectures.FieldTheory.TensorProductDiagonal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullbackCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullbackHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData

/-!
# Finite-field dualizing-object pullback

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: lem-sf-finite-field-dualizing-pullback).

The dualizing objects are specified by their constructible adjunction counits. The compact
support functors and exchange are the published compactification constructions, and the Hom
comparison is the evaluation transpose of the canonical tensorator.
-/

@[expose] public section
set_option autoImplicit false

universe u v w uC vC uD vD uB vB uB' vB'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The discrete condensed finite quotient coefficient of the finite-field comparison.
Source: blueprint finite-field paragraph, coefficient A
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDualizingCoefficient
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ) :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  let A := Padic.coefficientExtensionRing ell E n
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let R := Profinite.continuousMapRingObjOfUniverse.{u, u} A
  letI : MonObj R := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  letI : IsCommMonObj R := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
  exact CommMon.mk R

/-- The actual module-object derived category, with its relative derived tensor and Hom.
Source: blueprint finite-field paragraph, D(Mod A_V)
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
abbrev finiteFieldModuleDerived
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ.X X))

/-- The canonical dualizing-Hom comparison: evaluation transpose followed by Hom(1,w).
Source: blueprint finite-field paragraph, comparison c_K
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDualizingHomComparison
    {C : Type v} {D : Type w} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.Monoidal] (K W : C) (W' : D) (e : G.obj W ≅ W') :
    G.obj ((ihom K).obj W) ⟶ (ihom (G.obj K)).obj W' :=
  (Functor.LaxMonoidal.ihomComparison G K).natTrans.app W ≫ (ihom (G.obj K)).map e.hom

/-- The specified Koszul braiding on the actual module-object derived category.
Source: blueprint finite-field paragraph, symmetric tensor identifications
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDerivedBraiding
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) (K L : finiteFieldModuleDerived Λ X) : K ⊗ L ≅ L ⊗ K :=
  @BraidedCategory.braiding _ _ _
    (DerivedCategory.braidedCategory'
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) K L

/-- The finite-field comparison conclusions, expressed with categorical parameters so that
large derived-functor constructions are instantiated only once. In the theorem below every
category, functor, object property, braiding, and exchange is the specified published one.
The representing bijections specify the values of the constructible exceptional adjoints.
Source: blueprint finite-field paragraph, all displayed comparisons
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
structure FiniteFieldDualizingPullbackData
    {C : Type uC} {D : Type uD} {B : Type uB} {B' : Type uB'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vB} B] [Category.{vB'} B']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory B] [MonoidalCategory B']
    [MonoidalClosed C] [MonoidalClosed D]
    (constructible : ObjectProperty C) (ctf : ObjectProperty C) (ctfBar : ObjectProperty D)
    (G : C ⥤ D) [G.Monoidal] (H : B ⥤ B')
    (unitIso : H.obj (𝟙_ B) ≅ 𝟙_ B')
    (braid : ∀ K L : C, K ⊗ L ≅ L ⊗ K)
    (braidBar : ∀ K L : D, K ⊗ L ≅ L ⊗ K)
    (R : C ⥤ B) (Rbar : D ⥤ B') (alpha : R ⋙ H ⟶ G ⋙ Rbar) where
  W : C
  Wbar : D
  W_ctf : ctf W
  Wbar_ctf : ctfBar Wbar
  counit : R.obj W ⟶ 𝟙_ B
  counitBar : Rbar.obj Wbar ⟶ 𝟙_ B'
  represents : ∀ P : ctf.FullSubcategory,
    Function.Bijective (fun f : P.obj ⟶ W ↦ R.map f ≫ counit)
  representsBar : ∀ P : ctfBar.FullSubcategory,
    Function.Bijective (fun f : P.obj ⟶ Wbar ↦ Rbar.map f ≫ counitBar)
  symmetry : ∀ K L : C,
    Functor.LaxMonoidal.μ G K L ≫ G.map (braid K L).hom =
      (braidBar (G.obj K) (G.obj L)).hom ≫ Functor.LaxMonoidal.μ G L K
  preserves_ctf : ∀ K : ctf.FullSubcategory, ctfBar (G.obj K.obj)
  conservative : ∀ (K L : C) (f : K ⟶ L),
    constructible K → constructible L → IsIso (G.map f) → IsIso f
  exchange_iso : ∀ K : ctf.FullSubcategory, IsIso (alpha.app K.obj)
  dualizingIso : G.obj W ≅ Wbar
  counit_normalization : alpha.app W ≫ Rbar.map dualizingIso.hom ≫ counitBar =
    H.map counit ≫ unitIso.hom
  beta_iso : ∀ K : ctf.FullSubcategory,
    IsIso ((Functor.LaxMonoidal.ihomComparison G K.obj).natTrans.app W)
  comparison_iso : ∀ K : ctf.FullSubcategory,
    IsIso (finiteFieldDualizingHomComparison G K.obj W Wbar dualizingIso)
  comparison_natural : ∀ (K L : ctf.FullSubcategory) (f : L.obj ⟶ K.obj),
    G.map ((MonoidalClosed.pre f).app W) ≫
      finiteFieldDualizingHomComparison G L.obj W Wbar dualizingIso =
    finiteFieldDualizingHomComparison G K.obj W Wbar dualizingIso ≫
      (MonoidalClosed.pre (G.map f)).app Wbar
  evaluation : ∀ K : ctf.FullSubcategory,
    G.obj K.obj ◁ finiteFieldDualizingHomComparison G K.obj W Wbar dualizingIso ≫
      (ihom.ev (G.obj K.obj)).app Wbar =
    Functor.LaxMonoidal.μ G K.obj _ ≫ G.map ((ihom.ev K.obj).app W) ≫ dualizingIso.hom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Triangulatedness component of the finite-field comparison: the derived coefficient pullback
`G = L(g^*)` along `g : T ×_k k̄ → T` is triangulated.
Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(exactness of `G`).

Proof: module pullback is exact [det-prop-sfb-module-pullback-exact-main], so `L(g^*)` is
isomorphic to the levelwise functor `D(g^*)` [prop-sfb-module-left-derived-upper-star-levelwise],
which is triangulated; the published instance of `UpperStarShift` transports this structure.
(blueprint: new-lem-sf-finite-field-dualizing-pullback-triangulated) -/
theorem finiteField_dualizing_pullback_triangulated
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (E : Type u) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a] :
    (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
      (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).IsTriangulated := by
  -- Preserve the comparison API although exact pullback needs neither condition.
  have _ := hell
  have _ := hn
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
