/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists

/-! # The canonical Tate Frobenius scalar and additive comparisons

Source: proof Step 8 of the current coefficient-change blueprint.
(blueprint: lem-pur-condensed-tate-frobenius).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Preadditive
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.PurityCoefficientChange
open PurityTransport

private theorem ringInverse_eq_categoryInv {C : Type*} [Category C] [Preadditive C]
    {M : C} (f : End M) [IsIso f] : Ring.inverse f = inv f := by
  apply (cancel_mono f).mp
  rw [IsIso.inv_hom_id]
  exact Ring.mul_inverse_cancel f ((isUnit_iff_isIso f).mpr inferInstance)

private theorem integerInv_naturality {C E : Type*} [Category C] [Category E]
    [Preadditive C] [Preadditive E] (F : C ⥤ E) [F.Additive]
    (n : ℕ) (M : C) (N : E) (f : F.obj M ⟶ N)
    [IsIso (n • 𝟙 M)] [IsIso (n • 𝟙 N)] :
    F.map (inv (n • 𝟙 M)) ≫ f = f ≫ inv (n • 𝟙 N) := by
  apply (cancel_mono (n • 𝟙 N)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn : F.map (n • 𝟙 M) ≫ f = f ≫ (n • 𝟙 N) := by
    have hmap : F.map (𝟙 M) = 𝟙 (F.obj M) := F.map_id M
    rw [Functor.map_nsmul, hmap, nsmul_comp, Category.id_comp, comp_nsmul,
      Category.comp_id]
  rw [← hn, ← Category.assoc, ← F.map_comp, IsIso.inv_hom_id,
    F.map_id, Category.id_comp]

private theorem continuousScalar_isIso (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (n : ℕ) (hn : IsUnit (n : T)) :
    IsIso (n • 𝟙 (Profinite.continuousMapRingObj.{u} T)) := by
  let f := n • 𝟙 (Profinite.continuousMapRingObj.{u} T)
  have hS (S : Profinite.{u}ᵒᵖ) : IsIso (f.hom.app S) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : ULift.{u + 1} C(S.unop, T) ↦ n • x)
    have hu : IsUnit (n : ULift.{u + 1} C(S.unop, T)) := by
      simpa only [map_natCast] using
        (hn.map (ContinuousMap.C : T →+* C(S.unop, T))).map
          ULift.ringEquiv.symm.toRingHom
    simpa only [nsmul_eq_mul] using IsUnit.isUnit_iff_mulLeft_bijective.mp hu
  have : IsIso f.hom := NatIso.isIso_of_isIso_app f.hom
  have hf : IsIso ((sheafToPresheaf _ _).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (sheafToPresheaf _ _)

private theorem moduleScalar_isIso (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (n : ℕ) [IsIso (n • 𝟙 R)]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    IsIso (n • 𝟙 M) := by
  have hR : IsIso (n • 𝟙 (Mod.regular R)) := by
    have hf : IsIso ((Mod.forget R).map (n • 𝟙 (Mod.regular R))) := by
      change IsIso (n • 𝟙 R)
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget R)
  have : IsIso ((tensorRight M).map (n • 𝟙 (𝟙_ (Mod _ R)))) := inferInstance
  have : IsIso ((λ_ M).inv ≫ (tensorRight M).map (n • 𝟙 (𝟙_ (Mod _ R))) ≫
      (λ_ M).hom) := inferInstance
  simpa using this

private instance pointAdditive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem coefficientScalar_isIso (ell : ℕ) [Fact ell.Prime]
    (c : PurityTransport.Coefficient ell) (X : Scheme.{u}) (n : ℕ)
    (hn : ell.Coprime n)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X)) :
    IsIso (n • 𝟙 M) := by
  have hu : IsUnit (n : ℤ_[ell]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hn)
  have : IsIso (n • 𝟙 (Profinite.continuousMapRingObj.{u} ℤ_[ell])) :=
    continuousScalar_isIso _ n hu
  have hR : IsIso (n • 𝟙 (condensedRingObj
      (Profinite.continuousMapRingObj.{u} ℤ_[ell]) X)) := by
    simpa using (Functor.map_isIso (upperStarFromPoint X)
      (n • 𝟙 (Profinite.continuousMapRingObj.{u} ℤ_[ell])))
  let U : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[ell]) X) :=
    Mod.comap (coefficientMap
    (Λ := Profinite.continuousMapRingObj.{u} ℤ_[ell]) (Λ' := c.obj ell)
    (c.integralMap ell) X)
  have : IsIso (n • 𝟙 (U.obj M)) := moduleScalar_isIso X _ n _
  have hM : IsIso (U.map (n • 𝟙 M)) := by
    simpa using (inferInstance : IsIso (n • 𝟙 (U.obj M)))
  exact isIso_of_reflects_iso _ U

/-- The actual coefficient Tate lines have invertible q-power multiplication.
Source: Step 8 of the coefficient-change proof
(blueprint: lem-pur-condensed-tate-frobenius).
Proof: q is a power of the characteristic prime, distinct from ell, hence a unit
of the topological ring of ell-adic integers. On continuous-map sheaves its
multiplication is pointwise bijective. Pull back to the scheme, transfer from the
regular module to any module using the tensor unitor, and restrict scalars along
the constructed integral coefficient map. Restriction reflects isomorphisms.
This includes the zero power and the zero ring. -/
theorem tate_unit_invertible (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p) :
    TateUnitInvertible ell D := by
  intro c X d
  apply coefficientScalar_isIso ell c X (D.q ^ d)
  rw [D.cardinality_eq]
  exact ((Nat.coprime_primes (Fact.out : ell.Prime) D.prime).mpr hEll).pow_right _ |>.pow_right _

private theorem derivedTau_eq_inv (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ)
    [IsIso ((D.q ^ d) • 𝟙 (c.derivedLine ell X d))] :
    derivedTau ell D c X d = inv ((D.q ^ d) • 𝟙 (c.derivedLine ell X d)) := by
  have : IsIso (powerScalar ell D c X d) := tate_unit_invertible ell D hEll c X d
  dsimp only [derivedTau, tau]
  rw [ringInverse_eq_categoryInv]
  rw [Functor.map_inv, Functor.map_inv]
  congr 1
  let F : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X) ⥤
      c.derived ell X :=
    (DerivedCategory.singleFunctor _ 0) ⋙ shiftFunctor _ (2 * (d : ℤ))
  change F.map ((D.q ^ d) • 𝟙 (c.line ell X d)) = _
  rw [F.map_nsmul, F.map_id]
  rfl

/-- Every normalized coefficient and pullback comparison preserves the prescribed
q^(-d) Tate datum, without any flatness hypothesis on the coefficient map.
Source: Step 8 of the coefficient-change proof
(blueprint: lem-pur-condensed-tate-frobenius).
Proof: use invertibility of integer q-power multiplication on the line. In any
preadditive category every arrow intertwines integer multiplication and therefore
its inverse. Additive functors carry that inverse to the inverse integer scalar.
Apply this first after the single and shift functors, then to derived scalar
extension and its Tate comparison; apply it also to ordinary inverse image and
the specified pullback comparison. -/
theorem tate_frobenius_compatible (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (P : Coordinates.{u} ell) : FrobeniusCompatible ell D P := by
  have hu := tate_unit_invertible ell D hEll
  have hd (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
      IsIso ((D.q ^ d) • 𝟙 (c.derivedLine ell X d)) := by
    have : IsIso (powerScalar ell D c X d) := hu c X d
    let F : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X) ⥤
        c.derived ell X :=
      (DerivedCategory.singleFunctor _ 0) ⋙ shiftFunctor _ (2 * (d : ℤ))
    have hm : F.map (powerScalar ell D c X d) =
        (D.q ^ d) • 𝟙 (c.derivedLine ell X d) := by
      dsimp only [powerScalar]
      rw [F.map_nsmul, F.map_id]
      rfl
    rw [← hm]
    infer_instance
  refine ⟨hu, ?_, ?_⟩
  · intro c c' a ha X d
    have := hd c X d
    have := hd c' X d
    rw [derivedTau_eq_inv ell D hEll, derivedTau_eq_inv ell D hEll]
    have : (scalarSixChange a X).Additive := by
      have adj : scalarSixChange a X ⊣ _ :=
        Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)
      have : (scalarSixChange a X).IsLeftAdjoint := adj.isLeftAdjoint
      have : PreservesColimitsOfSize.{0, 0} (scalarSixChange a X) :=
        adj.leftAdjoint_preservesColimits
      have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (scalarSixChange a X)
      exact Functor.additive_of_preservesBinaryBiproducts _
    exact integerInv_naturality (scalarSixChange a X) (D.q ^ d)
      (c.derivedLine ell X d) (c'.derivedLine ell X d) _
  · intro c X Y f p d
    have : IsIso ((D.q ^ d) • 𝟙 (c.line ell X d)) := hu c X d
    have : IsIso ((D.q ^ d) • 𝟙 (c.line ell Y d)) := hu c Y d
    have : IsIso (powerScalar ell D c X d) := hu c X d
    have : IsIso (powerScalar ell D c Y d) := hu c Y d
    dsimp only [tau]
    rw [ringInverse_eq_categoryInv, ringInverse_eq_categoryInv]
    exact integerInv_naturality (CondensedRing.upperStar (c.obj ell) f) (D.q ^ d) _ _ _

end AlgebraicGeometry.ProEtale.PurityCoefficientChange
