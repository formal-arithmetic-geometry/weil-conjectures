/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison

/-!
# Finite-Tor direct image and change of finite coefficients

Source: blueprint main-20261015, smooth purity, reduction exceptional proof,
Locality and Charts; Bhatt--Scholze, Lemma 6.7.17 and Theorem 6.7.1
(blueprint: lem-pur-etale-finite-tor-direct-image-coefficients).

All categories are ordinary constant-ring module derived categories on small etale sites.
The scalar mate is the existing counit transpose, with its canonical projection normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open Padic
namespace AlgebraicGeometry.Etale

-- Match the quotient-ring instance path and keep canonical derived functors abstract.
attribute [local instance 20000] CommRing.toRing
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

/-- Finite-type direct image over an arbitrary positive-characteristic field has a uniform
all-module-sheaf bound and preserves bounded constructible finite-Tor complexes with the
indicated interval. Finite scalar extension preserves the interval on both schemes, and the
canonical B-linear counit mate is invertible and restricts to the projection morphism.

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-reduction,
reduction-exceptional proof, Locality and Charts; Bhatt--Scholze Lemma 6.7.17;
Stacks 0F10(1), 0F0Z, and 0GL6
(blueprint: lem-pur-etale-finite-tor-direct-image-coefficients).

Proof:
1. The DVR and finite-quotient statements lem-weil-l-adic-extension-integers-dvr and
lem-weil-valued-dvr-finite-quotients make A finite local Noetherian. Its residue field
and every finite A-algebra are finitely presented A-modules. The extending valuation
puts ell in (t), so ell^n kills A and B and is invertible in k.
2. Apply the relative clause of lem-kun-0f10 and def-kun-cd. Every A-module sheaf is
ell^n-torsion. The canonical restriction/direct-image comparison of
lem-sbc-canonical-restrict-scalars-functor-comparisons identifies its underlying higher
direct images with the abelian ones. Exact restriction detects zero, giving c_h.
3. Apply thm-dg-finite-type-constructibility to obtain bounded constructibility of Rh_*K;
its arbitrary-field statement allows nonseparated morphisms.
4. Set L = K tensor_A^L kappa. The Tor hypothesis bounds its cohomology in [a,b].
The module-sheaf categories are Grothendieck abelian and direct image is additive left
exact by lem-weil-pbc-module-sheaves-grothendieck-abelian and
lem-weil-pbc-module-direct-image-left-exact. The spectral sequence thm-sp-truncation-e2
has E2^{r,q} = R^r h_* H^q(L), supported in [0,c_h] times [a,b]. Its finite abutment
filtration therefore gives vanishing outside [a,b+c_h].
5. The finite-constant projection formula lem-sf-projection-finite-constant identifies
Rh_*L with Rh_*K tensor_A^L kappa. Apply lem-exc-residue-tor-test to deduce the
specified full Tor interval of Rh_*K.
6. The actual scalar extension of lem-pur-derived-change-of-rings has underlying
A-complex J tensor_A^L B. Evaluating the Tor bound at B shows it is bounded without
flatness. Restriction of scalars changes no cohomology groups.
7. Finite-type schemes over a field are Noetherian. Apply
lem-weil-pbc-finite-type-over-noetherian, det-pe-finite-tor-comparison-noetherian, and
det-sp-scalar-extension-functor to obtain constructibility and the unchanged B-Tor
interval after pro-etale comparison. The adjunction of
lem-pur-sheaf-ring-derived-coefficient-adjunction and uniqueness of left adjoints
identify the actual scalar functors with those in
lem-weil-pbc-derived-scalar-extension-local-systems. Essential surjectivity of the
finite-Tor comparison supplies an etale finite-Tor object. Both it and the actual
scalar extension are bounded below by step 6. Full faithfulness in
sk-prop-sf-comparison lifts their isomorphism, giving bounded constructibility;
the interval-detection clause gives precisely the original Tor interval.
8. Apply lem-pur-etale-scalar-mate-projection: the restricted mate followed by the
canonical direct-image restriction comparison is the specified projection map.
The finite-constant projection theorem makes that map invertible. The restriction
comparison is invertible on these bounded objects. Exact restriction reflects
isomorphisms, so the B-linear mate itself is invertible. -/
theorem finiteTor_directImage_coefficients
    (p l : ℕ) (_hp : 0 < p) [Fact l.Prime] (_hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (U V : Scheme.{u}) [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] :
    ∃ c : ℕ,
      (∀ (M : Sheaf U.smallEtaleTopology
          (ModuleCat.{u + 1} (coefficientExtensionRing l E n))) (q : ℕ), c < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) ∧
      (∀ (K : DerivedCategoryModule (coefficientExtensionRing l E n) U)
        (a b : ℤ), a ≤ b →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
          (finite_coefficientExtensionRing l E n hn) U K →
        DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) U a b K →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) V
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) V a (b + c)
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          ∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (φ : coefficientExtensionRing l E n →+* B),
            IsIso ((scalarMate φ h).app K) ∧
              (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).map
                  ((scalarMate φ h).app K) ≫
                  (scalarRestrictionDirectImageMap φ h).app ((scalarExtension φ U).obj K) =
                (scalarTensorIso φ V).hom.app
                    (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ≫
                  ((rightDerivedLowerStarProjectionMap
                    (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).app K).app
                    (scalarCoefficient φ V) ≫
                  R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).map
                    (((derivedTensor
                        (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) U).obj K).map
                        (scalarCoefficientPullbackIso φ h).hom ≫
                      (scalarTensorIso φ U).inv.app K)) ∧
      (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
        (φ : coefficientExtensionRing l E n →+* B)
        (W : Scheme.{u}), (W = U ∨ W = V) →
        ∀ (J : DerivedCategoryModule (coefficientExtensionRing l E n) W)
          (r s : ℤ), r ≤ s →
          @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) W J →
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) W r s J →
          DerivedCategory.isBoundedConstructible B W ((scalarExtension φ W).obj J) ∧
            DerivedCategory.hasTorAmplitudeIn B W r s ((scalarExtension φ W).obj J)) := by
  sorry

end AlgebraicGeometry.Etale
