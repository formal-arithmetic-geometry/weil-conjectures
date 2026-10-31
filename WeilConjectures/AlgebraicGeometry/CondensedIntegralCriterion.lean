/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE

import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBlueprint
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetectionSupplement

/-! # The four-way condensed integral constructibility criterion

Source: current blueprint, sec-proetale-coefficients/sk-prop-integral-criterion,
statement and all four proof paragraphs (blueprint: lem-fix-condensed-integral-criterion).

All categories and tensors are ordinary unbounded internal-module derived categories.
A finite free module over the condensed integer ring on the point is a finite sum of
its regular module. Maps between these sums are matrices over its sections on the
one-point profinite set, namely the scalar ring O_E. Thus a bounded complex of such
modules is precisely the continuous scalar realization of a bounded finite free
O_E-complex. Pulling it from the point gives B_U tensor over constant O_E with that
scalar complex. The matrices are chosen before the pullback to U, excluding arbitrary
B_U-valued matrices. This uses the existing finite-free and pullback constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Canonical scalar-complex realization on a chart: pull back the finite free point
complex termwise and localize. The additive and exact structures are supplied by the
existing finite-limit and left-adjoint properties of the inverse image from the point.
Source: current blueprint sk-prop-integral-criterion, condition (3)
(blueprint: lem-fix-condensed-integral-criterion). -/
noncomputable def condensedIntegralCriterionRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    CochainComplex
        (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ ⥤
      DerivedCategory (AdicCompletion.Modules l E X) := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
      AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
    dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteLimits (DerivedNakayama.pullback l E X) := by
    dsimp [DerivedNakayama.pullback]
    infer_instance
  have : (DerivedNakayama.pullback l E X).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (DerivedNakayama.pullback l E X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The four conditions of the integral criterion are equivalent, including torsion
scalar models, without a dimension bound or invertibility of the residue characteristic.
The third entry uses a finite constructible locally closed stratification and the actual
derived restriction along the composite chart-to-stratum-to-X morphism. Its point complex
is bounded termwise finite free; its scalar matrices and bounds can depend on the chart.
Source: current blueprint sk-prop-integral-criterion, conditions (1)--(4)
(blueprint: lem-fix-condensed-integral-criterion).

Proof plan, following the seven steps of the node:
1. The internal forward criterion lem-sfb-internal-integral-criterion-forward gives
   canonical quotient-tower completeness and bounded constructibility of the first
   derived reduction from bounded constructibility over B_X.
2. sk-prop-integral-local-structure turns completeness and the residue condition into
   the finite stratification and bounded finite free scalar chart complexes.
3. By lem-weil-l-adic-extension-integers-dvr the scalar ring is a PID. Apply
   lem-weil-pbc-pid-submodule-finite-basis to the cycles and boundaries in each finite
   free term: their quotient cohomology is finitely presented, even when torsion or zero,
   and vanishes outside the term bounds.
4. det-prop-sfb-qlbar-colimit-x-integral-limit identifies the coefficient ring with its
   quotient limit. Clause 1 of det-prop-integral-criterion-constant-coefficients gives
   flatness of constant-to-continuous scalars; lem-weil-pbc-finite-type-constant-exact
   gives exact constant sheafification. lem-sp-exact-functor-preserves-homology computes
   the realized cohomology. det-prop-sfb-module-pullback-exact-main and the coefficient
   isomorphism of sk-def-sfb-coefficient-morphisms identify it with restricted H^q(K).
5. Each stratum is quasi-compact. Choose finite affine open covers and, using the
   pro-etale covering condition, finitely many affine opens in the chart schemes whose
   images cover these opens. They still form a pro-etale cover: their fiber products
   with affine opens of the Noetherian stratum are quasi-compact opens of affine schemes.
   Exact restriction retains the scalar complexes. Take the minimum lower and maximum
   upper bounds over these finitely many charts and strata. The underlying abelian
   inverse images are the inverse images of the underlying module sheaves, so
   lem-weil-pbc-noetherian-stratum-detection gives global cohomological vanishing outside
   this interval. For the empty scheme use the interval [0,0].
6. The finitely presented scalar cohomology models give constructibility by
   sk-def-sfb-constructible; step 5 gives boundedness, proving (3) implies (1).
7. Noetherian X is qcqs. Clause 2 of lem-integral-ctf-equals-bc gives Tor amplitude
   [a-1,b] from integral bounded constructibility with cohomology in [a,b]. Its finite
   subextension formulation applies after embedding E into an algebraic closure.
   Conversely Dctf is contained in Dbc by det-def-sfb-constructible-tor-amplitude.
   Combine with steps 1, 2 and 6 to obtain all four equivalences. -/
theorem condensed_integral_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    List.TFAE [
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K,
      IsDerivedComplete l E X K ∧
        constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
          ((AdicCompletion.derivedReduction l E X 0).obj K),
      ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
        ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : U.I₀,
          ∃ (P : CochainComplex
              (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
                (DerivedNakayama.integerRing l E)) ℤ) (b c : ℤ),
            P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
            (∀ q : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X q)) ∧
            Nonempty
              ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
                  (U.f i ≫ S.immersion a)).mapDerivedCategory.obj K ≅
                (condensedIntegralCriterionRealization l E (U.X i)).obj P),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ∧
        DerivedCategory.finiteTorAmplitude _ K] := by
  sorry

end AlgebraicGeometry.ProEtale
