/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformConstructibleExtTorsion
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NoetherianStratifiedLattice
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformConstructibleExtIntegral
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison

/-!
# Uniform Ext vanishing with rational coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-rational.md and proof,
with the refined source cutoff recorded in the DAG
(blueprint: det-uniform-constructible-ext-rational).

The finite coefficient model, its adapted ordered stratification, and the integral
lattices are fixed before any target. A global integral lattice gives the original
source cutoff, without identifying it with the maximum of the refined cutoffs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The actual condensed inclusion of the recorded valuation ring in its finite field.
Source: blueprint rational Ext proof, coefficients E, and sk-lem-stratified-lattice
(blueprint: det-uniform-constructible-ext-rational). -/
def rationalExtIntegralInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ E) ⟶
      Profinite.continuousMapRingObj.{u} E :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)

/-- An integral lattice triple, bundled to keep the stratification interface small.
The monomorphism and rationalization refer to the same integral inclusion.
Source: blueprint rational Ext proof, coefficients E; sk-lem-stratified-lattice
(blueprint: det-uniform-constructible-ext-rational). -/
structure RationalExtIntegralLattice {T : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} [MonObj A] [MonObj B]
    [IsCommMonObj A] (α : A ⟶ B) [IsMonHom α]
    (LT : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) B) where
  /-- The integral module; A is the pulled O_E in both uses below. -/
  module_ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A
  locallyFree : CondensedRing.LocallyFree A module_
  inclusion : module_ ⟶ (Mod.comap α).obj LT
  mono_inclusion : Mono inclusion
  isIso_adjoint : IsIso (((Mod.extendRestrictAdjunction α).homEquiv
    module_ LT).symm inclusion)

/-- Refined source stratum data and its cohomological cutoffs. Source: blueprint
`det-uniform-constructible-ext-rational` (blueprint: det-uniform-constructible-ext-rational). -/
structure RationalUniformExtStrata (ℓ : ℕ) [Fact ℓ.Prime] (X S : Scheme.{u})
    (a : S ⟶ X) where
  stratification : X.FiniteLocallyClosedStratification
  /-- Empty strata are discarded, including for the empty-source convention. -/
  stratum_nonempty : ∀ r, (stratification.stratum r).Nonempty
  /-- Which strata lie in the locally closed source. -/
  sourceStratum : Fin stratification.n → Prop
  source_subset : ∀ r, sourceStratum r →
    stratification.stratum r ⊆ Set.range a
  complement_subset : ∀ r, ¬ sourceStratum r →
    stratification.stratum r ⊆ (Set.range a)ᶜ
  /-- The chosen order has open successive unions. -/
  successive_unions_open : ∀ m : Fin (stratification.n + 1),
    IsOpen (⋃ r : {r : Fin stratification.n // (r : ℕ) < (m : ℕ)},
      stratification.stratum r.1)
  closureScheme : Fin stratification.n → Scheme.{u}
  complement : Fin stratification.n → Scheme.{u}
  openFactor : ∀ r, stratification.domain r ⟶ closureScheme r
  closedFactor : ∀ r, closureScheme r ⟶ X
  complementMap : ∀ r, complement r ⟶ X
  openFactor_isOpen : ∀ r, IsOpenImmersion (openFactor r)
  closedFactor_isClosed : ∀ r, IsClosedImmersion (closedFactor r)
  complement_isOpen : ∀ r, IsOpenImmersion (complementMap r)
  complement_qc : ∀ r, QuasiCompact (complementMap r)
  complement_qs : ∀ r, QuasiSeparated (complementMap r)
  stratum_compact : ∀ r, CompactSpace (stratification.domain r)
  stratum_qsep : ∀ r, QuasiSeparatedSpace (stratification.domain r)
  factorization : ∀ r, openFactor r ≫ closedFactor r = stratification.immersion r
  hclosure : ∀ r, Set.range (closedFactor r) = closure (stratification.stratum r)
  hcomplement : ∀ r, Set.range (closedFactor r) = (Set.range (complementMap r))ᶜ
  cutoff : Fin stratification.n → WithTop ℕ
  cutoff_eq : ∀ r, cutoff r =
    @relativeCohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) _ _
        (complementMap r) (complement_qc r) (complement_qs r) +
      @cohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) (stratification.domain r)
        (stratum_compact r) (stratum_qsep r) + 2

end AlgebraicGeometry.ProEtale
