/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison
public import Sheaf.Paper.FiniteCoefficientFlatModel
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-! # The canonical internal-Hom comparison on constructible complexes

Source: Weil conjectures blueprint, sec-six-functors/sk-thm-sf-hom-ctf,
`thm-sf-hom-comparison-constructible.md`
(blueprint: thm-sf-hom-comparison-constructible).

The comparison is the existing `siteComparisonEvaluationHom`, obtained by transposing
pulled-back evaluation. Its termwise derived inverse image is identified with total left
derived inverse image by `leftDerivedFunctorIsoMapDerivedCategory`.
The coefficient ring is raised by its canonical `ULift` to the established module universe.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the canonical lift of the positive-level coefficient ring.
Source: Serre, Local Fields, II §2; blueprint coefficient conventions
(blueprint: thm-sf-hom-comparison-constructible). -/
noncomputable instance constructibleHomComparison_coefficientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
  (Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
    Padic.coefficientExtensionRing l E n).finite_iff.mpr
      (Padic.finite_coefficientExtensionRing l E n n.property)

/-- Finite-type schemes over the fixed algebraic closure satisfy the canonical Hom
comparison for a finite-Tor bounded constructible first input and an arbitrary bounded
constructible second input. Source: blueprint, sec-six-functors/sk-thm-sf-hom-ctf,
`thm-sf-hom-comparison-constructible.md`
(blueprint: thm-sf-hom-comparison-constructible).

Proof:
1. Finite type gives a finite affine open cover (lem-weil-pbc-qcqs-finite-affine-open-cover).
   Each member is finite type by lem-weil-pbc-lft-affine-pairs and separated by
   lem-weil-pbc-affine-source-morphism-separated; intersections need not be affine.
2. Open restriction is exact by lem-pur-site-restriction-module-adjunction-exact and
   preserves bounded constructibility by restricting a finite stratification. Choose
   a bounded flat model of K using lem-sf-flat-model. Its restrictions remain flat by
   lem-weil-pbc-slice-restriction-flat and keep the same bounds, hence finite Tor amplitude.
3. Derived Hom commutes with restriction: restrict a K-injective target using
   lem-pur-kinjective-restrict-localized. The sheaf-Hom products and differential of
   def-pur-hom-complex restrict termwise, giving the identification of def-pur-derived-internal-hom.
4. Comparison pullback commutes with restriction: the two composites of direct images
   agree on sections, so their left adjoints agree canonically. Exactness from
   lem-sf-comparison-pullback-exact gives the same identification on derived categories.
5. The restricted comparison is the comparison on the open. Restrict K-flat tensor
   representatives (lem-pc-kflat-resolution), the K-injective target, and evaluation.
   Tensor comparison from lem-weil-pbc-ringed-topoi-derived-tensor-pullback and currying
   from lem-sc-derived-hom-tensor-total are the same on pure tensors. Together with
   lem-pur-hom-kflat-into-kinjective and lem-pur-rhom-global-sections, transposition
   identifies the actual maps, not merely their endpoints.
6. Apply the internal-Hom clause of lem-weil-finite-duality-site-comparison on each affine.
   Its separated finite-type and input hypotheses were established in steps 1 and 2.
7. For each integer degree, the local inverses on cohomology agree on overlaps by
   uniqueness. Glue them by the sheaf axiom. Apply
   lem-weil-pbc-unbounded-derived-iso-cohomology to conclude. The empty cover and empty
   scheme are covered by the same sheaf axiom. No Tor condition is imposed on M. -/
theorem isIso_comparisonDerivedHom_of_constructible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n n.property)) X K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hM : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n n.property)) X M) :
    IsIso (siteComparisonEvaluationHom
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) X K M) := by
  sorry

end AlgebraicGeometry.ProEtale
