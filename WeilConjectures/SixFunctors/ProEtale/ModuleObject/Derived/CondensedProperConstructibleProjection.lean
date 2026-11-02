/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
public import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
public import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
public import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.PoincareDuality.ProjectionFormula
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperProjectionFormulaBounded
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-! # Proper projection with a finite-Tor second factor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 800000 in
-- The tensor and direct-image comparisons retain their derived instance arguments.
private theorem projection_second_tor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (C : Etale.DerivedCategoryModule A X) (D : Etale.DerivedCategoryModule A Y)
    (hC : Etale.DerivedCategory.isBoundedConstructible A X C)
    (_hD : Etale.DerivedCategory.isBoundedConstructible A Y D)
    (a b : ℤ) (hTor : Etale.DerivedCategory.hasTorAmplitudeIn A Y a b D) :
    ordinaryFiniteCoefficientProjectionIsIso A p
      (((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj C)
      (((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj D) := by
  refine (ordinaryFiniteCoefficientProjectionIsIso_iff A p _ _).2 ?_
  obtain ⟨c, d, hc⟩ := hC.2
  have hCplus : ∃ n : ℤ, C.IsGE n :=
    ⟨c, (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hc.2 i (Or.inl hi)⟩
  obtain ⟨e, f, hd⟩ := hC.2
  have hCge : C.IsGE e :=
    (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hd.2 i (Or.inl hi)
  let P := (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj D
  have hP : Etale.DerivedCategory.hasTorAmplitudeIn A X a b P :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A) p a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hTor))
  have hPC : (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj P).obj C).IsGE
      (a + e) := (DerivedCategory.isGE_iff _ _).2
    (Etale.derivedTensor_isZero_homology_of_torAmplitudeGE A X P C a e
      (fun M i hi ↦ hP M i (Or.inl hi)) ((DerivedCategory.isGE_iff _ _).1 hCge))
  have hTensor : ∃ n : ℤ,
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj C).obj P).IsGE n :=
    ⟨a + e, DerivedCategory.TStructure.t.isGE_of_iso
      (Etale.derivedTensorBraidingIso (ModuleCat.{u + 1} A) X P C) (a + e)⟩
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) p).app C).app D) :=
    Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
      A isAddTorsion_of_finite p C D
  have := ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived
    (ModuleCat.{u + 1} A) p C D hCplus hTensor
  exact isIso_app_app_of_iso
    (ProEtale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p)
    (((comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory).app
      C)
    (((comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory).app
      D)


set_option maxHeartbeats 800000 in
-- The fixed scalar and internal encodings carry large derived instance arguments.
private theorem projection_finite
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (K : ConstantModelBoundedConstructible Λ X.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y.left) :
    IsIso (moduleObjectProjectionMap Λ f.left K.obj L.obj) := by
  classical
  let E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T :=
    fun T ↦ (FiniteDiscreteOrdinary.encoding_exists A T).some
  let φ := coefficientMap e.inv.hom X.left
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) φ
  let K' := F.mapDerivedCategory.obj K.obj
  have hK' : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A)
      X.left K' := by
    refine ⟨F.bounded_mapDerivedCategory_obj K.property.1, fun n ↦ ?_⟩
    exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K.obj)
      (constructible_comap e.inv.hom X.left _ (K.property.2 n))
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨C, hC, ⟨j⟩⟩ :=
    (FiniteDiscreteOrdinary.ordinaryBC_iff A X.left _).mp
      (((FiniteDiscreteOrdinary.encoding_constructibility A X.left (E X.left)).2 _).mp hK')
  have hC' := (FiniteDiscreteOrdinary.etaleBC_iff A X.left C).mpr hC
  let originL := (coefficientEncoding_etaleOrigin (R := Λ) A ell k e E Y L).some
  have hproj := projection_second_tor (ULift.{u + 1} A) f.left C originL.1
    hC' originL.2.2.2.property.1 originL.2.1 originL.2.2.1 originL.2.2.2.property.2
  have hordinary := ordinaryFiniteCoefficientProjectionIsIso_of_iso
    (ULift.{u + 1} A) f.left j originL.2.2.2.val hproj
  have hinternal := (FiniteDiscreteOrdinary.finiteCoefficientProjectionEncoding A e E
    f.left K.obj L.obj).2 hordinary
  exact (finiteCoefficientProjectionIsIso_iff Λ f.left K.obj L.obj).1 hinternal

private theorem bounded_of_constant
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    (K : ConstantModelBoundedConstructible Λ T) :
    boundedConstructible (condensedRingObj Λ T) K.obj := by
  refine ⟨K.property.1, fun n ↦ ?_⟩
  apply constructible_of_finiteConstantStratified Λ T
  simpa only [IsConstantModelConstructible, if_pos
    (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)]
    using K.property.2 n

set_option maxHeartbeats 800000 in
-- The six coefficient cases retain the actual module-object projection comparisons.
/-- The ordinary proper projection arrow is invertible with a bounded constructible
first factor and a constructible finite-Tor second factor, at every admissible
coefficient. Source: current prop-functor-package, clause (5), and its proper
projection step; Stacks Tag 0F0G
(blueprint: lem-e6-condensed-proper-constructible-projection).

Proof: for finite coefficients, compare the canonical module-object adjunction
and tensor maps with the ordinary etale maps. Proper torsion projection makes
the latter invertible; the bounded constructible first factor has an etale
origin even when it has infinite Tor dimension. Only the second factor needs
a finite Tor interval in the comparison. For valuation-ring coefficients,
reduce the canonical map modulo each positive uniformizer power. Constructible
completeness and the residue criterion reflect invertibility. For finite
coefficient fields, rationalize the integral generators and extend over their
finite cones and shifts. Do the same after extension to the finite-subextension
algebraic-closure ring. Finally transport the actual map through coefficient
ring isomorphisms. The zero ring and zero inputs give isomorphisms of zero
objects. At no step is a finite-Tor hypothesis imposed on the first factor. -/
theorem condensedProperConstructibleProjection
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    [Fact (ell ≠ D.p)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (K : ConstantModelBoundedConstructible Λ X.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y.left) :
    IsIso (properProjectionMorphism Λ f.left K.obj L.obj) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  let : Fact (ringChar D.k ≠ ell) := ⟨by
    rw [ringChar.eq D.k D.p]
    exact (Fact.out : ell ≠ D.p).symm⟩
  apply (isIso_moduleObjectProjectionMap_iff Λ f.left K.obj L.obj).mp
  rcases hΛ with hfin | hZ | hQ | hE | hO | hbar
  · obtain ⟨A, _, _, _, _, hA, _, ⟨e⟩⟩ := hfin
    let : Finite A := hA
    obtain ⟨eA⟩ := liftCoefficientIso.{u} A
    exact projection_finite (ULift.{u} A) ell D.k Λ (e ≪≫ eA.symm) f K L
  all_goals
    let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    have hK := bounded_of_constant Λ X.left K
    have hL := bounded_of_constant Λ Y.left ⟨L.obj, L.property.1⟩
    apply projection_from_model ell D.k f _ K.obj L.obj hK hL
  · obtain ⟨e⟩ := hZ
    exact model_transport e (unitBall_model ell ℚ_[ell] (PadicInt.subring ell)
      (fun _ ↦ PadicInt.mem_subring_iff ell) D.k f)
  · obtain ⟨e⟩ := hQ
    exact model_transport e (continuous_model ell ℚ_[ell] D.k f)
  · obtain ⟨E, ⟨e⟩⟩ := hE
    exact model_transport e (rational_formula (Mon.mk (Profinite.continuousMapRingObj E))
      ell D.k f (Or.inl ⟨E, rfl⟩))
  · obtain ⟨E, ⟨e⟩⟩ := hO
    exact model_transport e (integral_model ell E D.k f)
  · obtain ⟨e⟩ := hbar
    exact model_transport e (rational_formula (Mon.mk (Profinite.padicAlgClRingObj ell))
      ell D.k f (Or.inr rfl))

end AlgebraicGeometry.ProEtale.CondensedRing
