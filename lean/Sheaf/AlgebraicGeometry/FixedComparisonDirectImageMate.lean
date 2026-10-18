/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity
import Sheaf.AlgebraicGeometry.ProEtale.BasisDerivedDetection
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Canonical direct-image mate in fixed coefficients

Source: blueprint, prop-weil-pbc-comparison-direct-image, first proof paragraph;
Stacks Project, Tags 099R and 0B65
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).

## Main definitions and statements

* `fixedComparisonPullbackPlus`: the canonical termwise pullback comparison.
* `fixedComparisonDirectImageMatePlus`: the canonical derived direct-image mate.
* `isIso_fixedComparisonDirectImageMatePlus`: its qcqs invertibility.
* `fixedComparisonDirectImageMatePlus_counit`: its specified counit normalization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The pullback comparison, induced termwise from the specified sheaf comparison.
Exact pro-etale pullback is its own left derived functor.
Source: Stacks Tags 099R and 0B65; blueprint comparison-direct-image proof
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate). -/
noncomputable def fixedComparisonPullbackPlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)).symm ≪≫
  Functor.mapDerivedCategoryPlusNatIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
  Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)

/-- The canonical derived direct-image mate of the underived counit comparison.
Its data is the existing right-derived base-change transformation, with its universal
property normalization, not a chosen isomorphism between the endpoints.
Source: Stacks Tags 099R and 0B65; blueprint comparison-direct-image proof
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate). -/
noncomputable def fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))

/-- Invertibility of the specified mate for a qcqs morphism.
Source: Stacks Tag 099R; blueprint comparison-direct-image proof
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).

Proof (the six steps of the node):
1. Form q by the inverse pullback comparison followed by the pulled-back etale
counit. The adjunction Hom bijection defines its unique mate b
(def-weil-pbc-adjunction-mate). The underived mate and right-derived base-change
construction give the displayed named transformation on injective representatives.
2. Naturality of the counit and pullback comparison gives naturality of q. Transpose
that identity under the adjunction to obtain naturality of b.
3. Restrict to affine opens of V. Both direct images evaluate over the same fibre
products, and restriction preserves injectives on both sites. The pullback comparison
and counit commute with these restrictions; hence the restricted b is the mate for
the restricted morphism. The sheaf axiom detects vanishing on this open cover.
4. On an affine ind-etale basis object W = lim W_i, put U_i = U times_V W_i.
The qcqs hypothesis makes each U_i qcqs, with affine transition maps. Fix one stage
and pass to its cofinal tail so the complexes are pullbacks of fixed-stage complexes.
Apply lem-weil-pbc-derived-cohomology-continuity twice. The middle identification
is the termwise equality of sections of etale direct image on an injective
representative, using lem-weil-pbc-etale-restriction-injectives.
5. Apply lem-weil-pbc-comparison-global-cohomology on U times_V W. Pro-etale
restriction preserves injectives, and exact inverse image makes its right adjoint
preserve injectives, so the resulting groups are the target's derived sections.
6. Represent K by etale injectives I and resolve A_U I into pro-etale injectives J.
The chain map is the transpose of the pulled-back counit followed by the resolution
map. Comparison pullbacks of injectives are section-acyclic on the basis
(lem-weil-pbc-comparison-injective-acyclicity), so Leray acyclicity permits evaluation
of that source complex. By lem-weil-pbc-comparison-sections its sections are the
filtered colimit of the sections over U_i. The counit sends each such section to
itself on its fibre product, followed by restriction to U times_V W and the comparison
and resolution maps. It is therefore precisely the continuity isomorphism of steps
4 and 5, compatibly with differentials and transitions. The named map is invertible
by lem-weil-pbc-basis-derived-detection. The counit normalization is stated below. -/
theorem isIso_fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (fixedComparisonDirectImageMatePlus Λ f) := by
  sorry

/-- The specified counit-mate normalization. It also characterizes the named component
as the adjoint transpose of the pulled-back etale counit after inverse pullback comparison.
Source: Stacks Tag 0B65; blueprint comparison-direct-image proof, first paragraph
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).

Proof: the underived comparison is defined by the sheaf counit mate. Apply the exact
comparison and inverse-image functors termwise to bounded-below injective representatives.
The defining right-derived base-change factorization descends the same mate identity.
The derived adjunction triangle identities cancel the inserted unit and counit, giving
this formula. The adjunction Hom bijection then identifies this component with the
transpose specified in the node. Naturality is built into the transformation. -/
theorem fixedComparisonDirectImageMatePlus_counit (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fixedComparisonPullbackPlus Λ f).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ f).app K) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  sorry

end AlgebraicGeometry.ProEtale
