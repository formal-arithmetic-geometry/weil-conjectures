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
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-! # Uniqueness of the normalized scalar Tate coordinates

Source: balanced-tensor normalization in Step 7 of the coefficient-change proof.
(blueprint: lem-pur-condensed-scalar-coordinates-unique).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.PurityCoefficientChange
open PurityTransport

private theorem monoidal_eq_of_delta {C E : Type*} [Category C] [Category E]
    [MonoidalCategory C] [MonoidalCategory E] (F : C ⥤ E) (m n : F.Monoidal)
    (hd : ∀ M N, m.toOplaxMonoidal.δ M N = n.toOplaxMonoidal.δ M N) : m = n := by
  letI := m
  have hu : m.toOplaxMonoidal.η = n.toOplaxMonoidal.η := by
    apply Functor.eq_of_leftUnitality (m.toOplaxMonoidal.δ (𝟙_ C) (𝟙_ C))
    · exact Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ C)
    · rw [hd]
      exact @Functor.OplaxMonoidal.left_unitality_hom _ _ _ _ _ _ F
        n.toOplaxMonoidal (𝟙_ C)
  have hmu (M N : C) : m.toLaxMonoidal.μ M N = n.toLaxMonoidal.μ M N := by
    apply (cancel_mono (m.toOplaxMonoidal.δ M N)).mp
    rw [Functor.Monoidal.μ_δ, hd]
    exact (@Functor.Monoidal.μ_δ _ _ _ _ _ _ F n M N).symm
  have he : m.toLaxMonoidal.ε = n.toLaxMonoidal.ε := by
    apply (cancel_mono m.toOplaxMonoidal.η).mp
    rw [Functor.Monoidal.ε_η, hu]
    exact (@Functor.Monoidal.ε_η _ _ _ _ _ _ F n).symm
  apply Functor.Monoidal.ext
  · exact he
  · exact funext fun M ↦ funext fun N ↦ hmu M N
  · exact hu
  · exact funext fun M ↦ funext fun N ↦ hd M N

private def ScalarUnitNormalized (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell) (X : Scheme.{u})
    (m : (Mod.extendScalars
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).Monoidal) : Prop :=
  ∀ M N, Mod.tensorObjπ M N ≫
      (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
        a.hom.hom X) (M ⊗ N)).hom ≫ (m.toOplaxMonoidal.δ M N).hom =
    ((Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) M).hom ⊗ₘ
      (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
        a.hom.hom X) N).hom) ≫
      Mod.tensorObjπ
        ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
          a.hom.hom X)).obj M)
        ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
          a.hom.hom X)).obj N)

private theorem normalized_monoidal_unique (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell) (X : Scheme.{u})
    (m n : (Mod.extendScalars
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).Monoidal)
    (hm : ScalarUnitNormalized ell a X m) (hn : ScalarUnitNormalized ell a X n) : m = n := by
  apply monoidal_eq_of_delta
  intro M N
  apply (Mod.extendHomEquiv
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X) (M ⊗ N) _).injective
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ M N)).mp
  exact (hm M N).trans (hn M N).symm

private theorem line_eq_rec (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) (d : ℕ) :
    c.line ell X d = Nat.rec (𝟙_ _) (fun _ N ↦ N ⊗ c.firstLine ell X) d := by
  induction d with
  | zero => rfl
  | succ d hd => change c.line ell X d ⊗ _ = _; rw [hd]

private theorem castIso_heq {C : Type*} [Category C]
    {M M' N N' : C} (hM : M = M') (hN : N' = N) (e : M' ≅ N') :
    HEq (eqToIso hM ≪≫ e ≪≫ eqToIso hN) e := by
  cases hM
  cases hN
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  exact HEq.rfl

/-- The normalized scalar Tate coordinates exist before any geometric purity
or trace argument. Source: balanced tensor powers in coefficient-change Step 7
(blueprint: lem-pur-condensed-scalar-coordinates-unique).
Proof: take the explicit scalar-association comparison of the first line. A
scalar-unit-normalized monoidal structure on extension of scalars exists by the
balanced tensor universal property. Use it to define every tensor power, including
its unit at zero. The same universal property identifies the tensor comparison
of any two normalized structures; the monoidal unit axioms then identify their
unit comparisons. Thus the powers have the required normalization for every
normalized monoidal structure, not just the one used to construct them. -/
theorem scalarLineCoordinates_nonempty (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    Nonempty (ScalarLineCoordinates ell a ha X) := by
  obtain ⟨m, hm⟩ := Mod.exists_extendScalarsMonoidal
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)
  letI := m
  refine ⟨{ first := scalarFirst ell a ha X
            first_normalized := HEq.rfl
            power := fun d ↦
              eqToIso (congrArg (Mod.extendScalars (coefficientMap
                (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).obj
                  (line_eq_rec ell c X d)) ≪≫ powerPull
              (Mod.extendScalars (coefficientMap
                (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X))
              (c.firstLine ell X) (c'.firstLine ell X) (scalarFirst ell a ha X) d ≪≫
              eqToIso (line_eq_rec ell c' X d).symm
            power_normalized := ?_ }⟩
  intro n hn d
  have hmn : m = n := normalized_monoidal_unique ell a X m n hm hn
  cases hmn
  exact castIso_heq _ _ _

/-- The first-line comparison and normalized tensor powers leave no scalar
coordinate choices. Source: Step 7 of the coefficient-change proof
(blueprint: lem-pur-condensed-scalar-coordinates-unique).
Proof: first-line normalization fixes the first isomorphism. Choose a proven
scalar-unit-normalized monoidal structure on scalar extension and evaluate both
power normalization equations at this same structure. They identify every power.
The remaining fields are propositions and hence proof irrelevant. -/
theorem scalarLineCoordinates_subsingleton (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    Subsingleton (ScalarLineCoordinates ell a ha X) := by
  obtain ⟨m, hm⟩ := Mod.exists_extendScalarsMonoidal
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)
  refine ⟨fun p q ↦ ?_⟩
  have hf : p.first = q.first := eq_of_heq (p.first_normalized.trans q.first_normalized.symm)
  have hp : p.power = q.power := by
    funext d
    apply eq_of_heq
    exact (p.power_normalized m hm d).trans
      ((heq_of_eq (congrArg (fun e ↦ @powerPull _ _ _ _ _ _ _ m
        (c.firstLine ell X) (c'.firstLine ell X) e d) hf)).trans
          (q.power_normalized m hm d).symm)
  cases p
  cases q
  dsimp only at hf hp
  subst_vars
  rfl

/-- The global coefficient coordinates also have no choices.
Source: Step 7 of the coefficient-change proof
(blueprint: lem-pur-condensed-scalar-coordinates-unique).
Proof: integral compatibility is a proposition, so its proof families are equal.
For each coefficient arrow and scheme the preceding uniqueness theorem then
identifies the line coordinates. Function extensionality and structure
extensionality identify the two global coordinate records. -/
theorem coordinates_subsingleton (ell : ℕ) [Fact ell.Prime] :
    Subsingleton (Coordinates.{u} ell) := by
  refine ⟨fun p q ↦ ?_⟩
  cases p with
  | mk integral line =>
    cases q with
    | mk integral' line' =>
      congr 1
      funext c c' a ha X
      exact @Subsingleton.elim _ (scalarLineCoordinates_subsingleton ell a _ X) _ _

private theorem source_tensor_naturality {C C' E E' : Type*}
    [Category C] [Category C'] [Category E] [Category E']
    [MonoidalCategory E] [MonoidalCategory E']
    (H : C ⥤ E) (H' : C' ⥤ E') (TX : E ⥤ E') [TX.Monoidal] (TY : C ⥤ C')
    (p : H ⋙ TX ⟶ TY ⋙ H') (L : E) (N : E') (l : TX.obj L ⟶ N)
    {K K' : C} (v : K ⟶ K') :
    TX.map ((tensorRight L).map (H.map v)) ≫
        (Functor.Monoidal.μIso TX (H.obj K') L).inv ≫ (p.app K' ⊗ₘ l) =
      (Functor.Monoidal.μIso TX (H.obj K) L).inv ≫ (p.app K ⊗ₘ l) ≫
        (tensorRight N).map (H'.map (TY.map v)) := by
  have hn := p.naturality v
  change TX.map (H.map v) ≫ p.app K' = p.app K ≫ H'.map (TY.map v) at hn
  change TX.map (H.map v ▷ L) ≫ Functor.OplaxMonoidal.δ TX _ _ ≫ _ =
    Functor.OplaxMonoidal.δ TX _ _ ≫ _ ≫ (H'.map (TY.map v) ▷ N)
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id]
  rw [hn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Normalize the two exposed presentations of the same tensorator and pullback composite.
end AlgebraicGeometry.ProEtale.PurityCoefficientChange
