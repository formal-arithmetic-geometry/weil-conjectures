/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComparisonDefinitions
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComparisonDefinitions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StandingFieldCtfStability

/-! # Native condensed field projection comparison equations

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, final coherence sentence, expanded in
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-common-projection-comparison-equations).

All maps live in the ordinary uncompleted derived categories of internal modules.
The normalized comparison data are those of the native composition theorem.
The full finite-Tor category equals the full bounded constructible category at
both field coefficients, by integral_ctf_equals_bc. No projection is inverted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace NativeFieldProjection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Include the recorded finite-Tor full subcategory in its localizing closure.
Source: the source proof, Step 5, restriction of the ambient comparisons
(blueprint: lem-sf-common-projection-comparison-equations). -/
def toLocalizing {X : Scheme.{u}} (K : ConstantModelConstructibleFiniteTor Λ X) :
    (localizingClosureProEtale Λ X).FullSubcategory :=
  ⟨K.obj, fun _P _ hP ↦ hP K.obj K.property⟩

/-- The proper identity-open compactification is canonically the ordinary direct image.
Source: the source proof, Step 4, the compactification (id,f)
(blueprint: lem-sf-common-projection-comparison-equations). -/
def properModelIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper f) ≅
      (lowerStar Λ f).rightDerivedFunctor :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X) _ ≪≫
    Functor.leftUnitor _

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓp : ℓ ≠ D.p)
  (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))

include hℓp hΛ

/-- The tensor input of every comparison remains in the recorded finite-Tor category.
This is the typing assertion used when evaluating a localizing comparison at that input.
Source: the source proof, Step 5
(blueprint: lem-sf-common-projection-comparison-equations).
Proof: the algebraic closure D.k has ell-cohomological dimension zero. The native
six-functor stability theorem therefore preserves Dctf under pullback and tensor.
Apply its pullback clause to L, and its tensor clause to K and that pullback.
The coefficient isomorphisms in hΛ identify the prescribed integral and field coefficients;
integral_ctf_equals_bc identifies Dctf with Dbc without a completeness condition. -/
theorem tensor_mem {X Y : SepFinType D.k} (f : X ⟶ Y)
    (K : ConstantModelConstructibleFiniteTor Λ X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y.obj.left) :
    (constantModelBoundedConstructible Λ X.obj.left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (K.obj ⊗ (moduleObjectDerivedPullback Λ f.hom.left).obj L.obj) := by
  classical
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨by
    rw [ringChar.eq D.k D.p]
    exact D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) := ⟨by
    rw [ringChar.eq D.k D.p]
    exact hℓp.symm⟩
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hcoeff : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hΛ with h | h
    · obtain ⟨E, h | h⟩ := h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  let : X.obj.left.Over (Spec (.of D.k)) := ⟨X.obj.hom⟩
  let : Y.obj.left.Over (Spec (.of D.k)) := ⟨Y.obj.hom⟩
  let : f.hom.left.IsOver (Spec (.of D.k)) := ⟨f.hom.w⟩
  let : LocallyOfFiniteType (X.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType X.obj.hom)
  let : QuasiCompact (X.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact X.obj.hom)
  let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (IsSeparated X.obj.hom)
  let : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.obj.hom)
  let : QuasiCompact (Y.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact Y.obj.hom)
  let : IsSeparated (Y.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (IsSeparated Y.obj.hom)
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) :=
    f.hom.w.symm ▸ inferInstanceAs (IsSeparated X.obj.hom)
  let : IsSeparated f.hom.left := IsSeparated.of_comp f.hom.left Y.obj.hom
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) :=
    f.hom.w.symm ▸ inferInstanceAs (LocallyOfFiniteType X.obj.hom)
  let : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
  let : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  let : QuasiSeparatedSpace Y.obj.left := quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  let : QuasiCompact f.hom.left := inferInstance
  obtain ⟨hpull, htensor, _⟩ :=
    constructibleFiniteTor_stability_direct_images_of_finite_or_isAlgClosed ℓ D.k
      (Or.inr inferInstance) Λ hcoeff f.hom.left
  exact htensor K.obj _ K.property (hpull L.obj L.property)

/-- The tensor input as an object of the comparison's localizing source.
Source: the source proof, Step 5
(blueprint: lem-sf-common-projection-comparison-equations). -/
def tensorLocalizing {X Y : SepFinType D.k} (f : X ⟶ Y)
    (K : ConstantModelConstructibleFiniteTor Λ X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y.obj.left) :
    (localizingClosureProEtale Λ X.obj.left).FullSubcategory :=
  toLocalizing Λ ⟨_, tensor_mem Λ D ℓ hℓp hΛ f K L⟩

end NativeFieldProjection
end AlgebraicGeometry.ProEtale.CondensedRing
