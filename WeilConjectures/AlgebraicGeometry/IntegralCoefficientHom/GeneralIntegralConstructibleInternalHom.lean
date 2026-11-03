/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
import WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.CondensedIntegralHom.CondensedIntegralHomReductionComparisonIso
import WeilConjectures.AlgebraicGeometry.CondensedIntegralHom.CondensedIntegralHomReductionCompleteness
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientHom.IntegralConstructibleInternalHomBounded
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientHom.IntegralConstructibleInternalHomData
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientHom.IntegralConstructibleInternalHomTor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed

/-! # Integral constructible internal Hom for arbitrary admissible integral rings

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
cor-coef-integral-internal-hom.md and its proof, order 2992
(blueprint: cor-coef-integral-internal-hom).

All categories are ordinary derived categories of modules over pulled-back condensed
rings. The scalar maps below are the actual quotient maps, at exponent n itself.
No extension field or coefficient presentation is chosen in their construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralCoefficientHom

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Continuous postcomposition by the quotient map R → R/(π^n).
Source: latest blueprint cor-coef-integral-internal-hom, coefficient reductions
(blueprint: cor-coef-integral-internal-hom). -/
def quotientRingSheafMap (π : R) (n : ℕ) :
    Profinite.continuousCoefficientRingSheaf R ⟶
      Profinite.continuousCoefficientRingSheaf (R ⧸ Ideal.span ({π ^ n} : Set R)) :=
  ⟨{
    app := fun _ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((Ideal.Quotient.mk (Ideal.span ({π ^ n} : Set R))).compLeftContinuous _
        continuous_quot_mk).comp ULift.ringEquiv.toRingHom))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The same quotient map as a morphism of condensed ring objects.
Source: latest blueprint cor-coef-integral-internal-hom, A_n = R/(π^n)
(blueprint: cor-coef-integral-internal-hom). -/
abbrev quotientMap (π : R) (n : ℕ) :
    Profinite.continuousCoefficientRingObj R ⟶
      Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R)) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (quotientRingSheafMap R π n)

/-- Derived extension along p_X^* of the actual coefficient quotient map.
This has values in modules over A_(n,X), retaining their quotient scalar action.
Source: latest blueprint cor-coef-integral-internal-hom, definition of M_n
(blueprint: cor-coef-integral-internal-hom). -/
abbrev reduction (X : Scheme.{u}) (π : R) (n : ℕ) :=
  (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedFunctor

/-- The canonical scalar tensor comparison, obtained on K-flat representatives.
Source: latest blueprint cor-coef-integral-internal-hom, evaluation comparison;
lem-coef-integral-hom-reduction.proof.md, first paragraph
(blueprint: cor-coef-integral-internal-hom). -/
def reductionTensorIso (X : Scheme.{u}) (π : R) (n : ℕ)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))) :
    (reduction R X π n).obj (K ⊗ L) ≅
      (reduction R X π n).obj K ⊗ (reduction R X π n).obj L :=
  letI := Mod.extendScalarsMonoidal (coefficientMap (quotientMap R π n) X)
  letI := Mod.extendScalars_preservesFlat (coefficientMap (quotientMap R π n) X)
  let τ := asIso
    (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedTensorComparison
  (τ.app K).app L

/-- The canonical evaluation-defined comparison H_n → RHom_(A_n)(K_n,L_n).
It is the transpose of inverse scalar tensor comparison followed by reduced evaluation.
Its definition includes no invertibility assertion about the Hom comparison.
Source: latest blueprint cor-coef-integral-internal-hom, comparison clause
(blueprint: cor-coef-integral-internal-hom). -/
def comparison (X : Scheme.{u}) (π : R) (n : ℕ)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))) :
    (reduction R X π n).obj
        (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
          (op K)).obj L) ⟶
      ((CondensedRing.derivedHom
        (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R))) X).obj
          (op ((reduction R X π n).obj K))).obj ((reduction R X π n).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction
    (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R)))
      ((reduction R X π n).obj K)).homEquiv _ _
    ((reductionTensorIso R X π n K
      (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
        (op K)).obj L)).inv ≫
      (reduction R X π n).map
        ((CondensedRing.derivedTensorHomAdjunction
          (Profinite.continuousCoefficientRingObj R) K).counit.app L))

/-- Integral bounded constructible internal Hom, canonical finite reductions, and
uniform Tor bounds for every admissible integral coefficient ring and standing base field.
The coefficient admissibility premise is precisely the two integral alternatives of
IsLocalizingAdmissibleCoefficient on the condensed ring associated to R; no E,
isomorphism or presentation is fixed. An irreducible element of an
admissible integral ring is exactly a uniformizer. Quotient topologies are discrete here.

Source: latest blueprint cor-coef-integral-internal-hom.md and its three-step DAG proof
(blueprint: cor-coef-integral-internal-hom).

Proof:
1. Finite type over a field makes X Noetherian. The canonical reduction and integral
   residue test give invertibility of every specified comparison and a residue test
   for bounded constructibility of H.
2. The residue-Tor theorem makes the input reductions finite-Tor. Finite coefficient
   constructible Hom makes T_n bounded constructible. In particular H_1 is bounded
   constructible through its specified comparison with T_1. The residue test gives
   bounded constructibility of H.
3. Apply the quantitative finite Hom estimate directly to the supplied reduction Tor
   intervals and d. Transport its interval along the actual comparison at every n. -/
theorem boundedConstructible_internalHom
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (_hk : Finite k ∨ IsAlgClosed k) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (_hR :
      Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
        Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
          Mon.mk (Profinite.padicIntegersRingObj ℓ E)))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (π : R) (_hπ : Irreducible π)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)))
    (_hK : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) K)
    (_hL : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) L) :
    boundedConstructible (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)
        (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
          (op K)).obj L) ∧
      (∀ (n : ℕ), 1 ≤ n → IsIso (comparison R X π n K L)) ∧
      ∀ (a b c e : ℤ), a ≤ b → c ≤ e →
        ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
          (∀ (n : ℕ), 1 ≤ n → _root_.DerivedCategory.torAmplitudeIn _ a b
            ((reduction R X π n).obj K)) →
          (∀ (n : ℕ), 1 ≤ n → _root_.DerivedCategory.torAmplitudeIn _ c e
            ((reduction R X π n).obj L)) →
          ∀ (n : ℕ), 1 ≤ n → _root_.DerivedCategory.torAmplitudeIn _
            (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
            ((reduction R X π n).obj
              (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
                (op K)).obj L))  := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  obtain ⟨hcomparison, htest⟩ :=
    admissible_integral_hom_residue_test R ℓ _hR X π _hπ K L _hK _hL
  obtain ⟨hfinite, htor⟩ :=
    admissible_finite_hom_bound R k p _hk ℓ _hℓ _hR X π _hπ K L _hK _hL
  have : IsIso (comparison R X π 1 K L) := hcomparison 1 le_rfl
  refine ⟨htest ((boundedConstructible _).prop_of_iso
    (asIso (comparison R X π 1 K L)).symm (hfinite 1 le_rfl)), hcomparison, ?_⟩
  intro a b c e hab hce d hd hKt hLt n hn
  have := hcomparison n hn
  exact (_root_.DerivedCategory.torAmplitudeIn _ _ _).prop_of_iso
    (asIso (comparison R X π n K L)).symm (htor a b c e hab hce d hd hKt hLt n hn)

end AlgebraicGeometry.ProEtale.IntegralCoefficientHom
