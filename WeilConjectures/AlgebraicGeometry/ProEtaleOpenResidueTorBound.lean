/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.FiniteConstantProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProjectionComparisonEtaleProEtale
public import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
public import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement

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
import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.OpenImmersionHigherDirectImages
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.ResidueTorAmplitudeTest
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit

/-!
# Residue projection and the pro-etale open-image Tor bound

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, (1 prime) and Projection formula for kappa
(blueprint: lem-sf-proetale-open-residue-tor-bound).

The assertion is packaged as a proposition to pass the derived finiteness instance
explicitly. Its maps are the published adjunction projection and direct-image mate.
Fixed module sheaves are used throughout, including the Tor tests against every
pro-etale module sheaf. The published intrinsic realization equivalence identifies this
with the intrinsic constant-ring presentation, without restricting test sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The degree-zero residue module in the common coefficient universe. This is the
ordinary quotient by the image of the uniformizer, with its quotient scalar action.
Source: blueprint, Projection formula for kappa
(blueprint: lem-sf-proetale-open-residue-tor-bound). -/
noncomputable def openResidueModule (A : Type u) [CommRing A] (r : A) :
    ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
  ModuleCat.of (ULift.{u + 1, u} A)
    ((ULift.{u + 1, u} A) ⧸ Ideal.span ({ULift.up r} : Set (ULift.{u + 1, u} A)))

/-- The published bounded-below direct-image mate in the unbounded categories,
with precisely the standard endpoint compatibility isomorphisms, in their stated order.
Source: blueprint, Projection formula for kappa; canonical comparisons
(blueprint: lem-sf-proetale-open-residue-tor-bound). -/
noncomputable def openResidueDirectImageMate (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (F : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj F.obj) ⟶
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj F.obj) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
    ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.inv.app F) ≫
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.inv.app
    ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj F) ≫
  _root_.DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A j).app F) ≫
  (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.hom.app
    ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj F) ≫
  (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.map
    ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlusCompatibility.hom.app F)

/-- The two explicit canonical routes in the projection square. The first pulls back
pi_et and then uses the direct-image mate and the monoidal pullback comparison. The
second first uses the monoidal comparison and the direct-image mate, then pi_proet.
All factors are specified natural transformations, so the square is natural in F.
Source: blueprint, Projection formula for kappa
(blueprint: lem-sf-proetale-open-residue-tor-bound). -/
def openResidueProjectionSquare (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (F : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (N : Etale.DerivedCategoryModule A X)
    (hL : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) U).obj F.obj).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N))) : Prop :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app F.obj).app N) ≫
    openResidueDirectImageMate A j ⟨_, hL⟩ ≫
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.map
      (comparisonOpenTensorIso A j F.obj N).hom =
  ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj F.obj)).app N).hom ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
      (openResidueDirectImageMate A j F)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj N) ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj F.obj)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj N)

/-- The open-residue conclusion as a predicate of a coefficient module. This predicate
is asserted below only for the actual residue quotient. Tor amplitude tests every
pro-etale module sheaf; no perfectness of the coefficient module is imposed.
Source: blueprint, (1 prime) and Projection formula for kappa
(blueprint: lem-sf-proetale-open-residue-tor-bound). -/
def openResidueFixedTorBoundAssertion (A : Type (u + 1)) [CommRing A] [Finite A]
    (M₀ : ModuleCat.{u + 1} A)
    {U X : Scheme.{u}} (j : U ⟶ X) : Prop :=
  ∀ (N : ℕ),
    (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℕ), N < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) →
  ∀ (a b : ℤ), a ≤ b →
  ∀ (G : _root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))),
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) U G →
    DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} A) U a b G →
  ∀ (F : _root_.DerivedCategory.Plus
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))),
    Etale.DerivedCategory.isBoundedConstructible A U F.obj →
  ∀ (e : (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
    F.obj ≅ G),
    IsIso ((Etale.finiteConstantProjectionMap A j F.obj).app M₀) ∧
    (∀ q : ℤ, (q < a ∨ b + (N : ℤ) < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) U).obj F.obj).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf U.smallEtaleTopology
                (ModuleCat.{u + 1} A)).obj M₀)))))) ∧
    Etale.DerivedCategory.isBoundedConstructible A X
      ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
        F.obj) ∧
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
      ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj G) ∧
    DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} A) X a (b + N)
      ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj G) ∧
    (∃ hL : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) U).obj F.obj).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj
           ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} A)).obj M₀)))),
      IsIso (openResidueDirectImageMate A j F) ∧
      IsIso (openResidueDirectImageMate A j ⟨_, hL⟩) ∧
      openResidueProjectionSquare A j F
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj M₀)) hL) ∧
    (∀ (F₁ : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))),
      Etale.DerivedCategory.isBoundedConstructible A U F₁.obj →
      ∀ e₁ : (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
        F₁.obj ≅ G,
      ∃! v : F.obj ≅ F₁.obj,
        (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.map
          v.hom ≫ e₁.hom = e.hom)

/-- The canonical residue projection is invertible, its target lies in [a,b+N], and
open direct image preserves bounded constructibility with this all-module Tor interval.
The assertion also records the canonical comparison square and independence of origin.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, (1 prime) and Projection formula for kappa
(blueprint: lem-sf-proetale-open-residue-tor-bound).

Proof:
1. The coefficient DVR has finite residue field; its positive quotients are finite local
Noetherian rings. The presentation A --varpi--> A --> kappa --> 0 proves finite
presentation, also at n=1. Finite type over k makes X Noetherian; its open U is
Noetherian. Thus j is quasi-compact, and as an open monomorphism it is separated, hence
quasi-separated. Use lem-weil-l-adic-extension-integers-dvr,
lem-weil-valued-dvr-finite-quotients, def-sc-finitely-presented-module,
lem-weil-pbc-finite-type-over-noetherian and
lem-weil-pbc-noetherian-open-subscheme-noetherian.
2. By lem-exc-comparison-tor-interval, the arbitrary bounded-below origin F has etale
Tor amplitude [a,b]. Testing the residue sheaf gives F tensor kappa in that interval
(def-kun-tor-amplitude); tensoring with kappa was not assumed to preserve boundedness.
3. Apply lem-sf-projection-finite-constant to j, F and the finitely presented kappa.
Its all-module dimension bound is the hypothesis N. Its canonical map is exactly
def-kun-projection-formula-map followed by the constant inverse-image identification.
4. The truncation spectral sequence thm-sp-truncation-e2 has p in [0,N] and q in [a,b],
so Rj_*(F tensor kappa) lies in [a,b+N]. Apply the same spectral sequence to F;
thm-fin-open-immersion and thm-constructible-serre make Rj_*F bounded constructible.
Now lem-exc-residue-tor-test gives etale Tor amplitude [a,b+N]. Module sheaves are
Grothendieck abelian by lem-weil-pbc-module-sheaves-grothendieck-abelian.
5. The qcqs mate lem-weil-pbc-comparison-direct-image-canonical-mate identifies the
comparison of Rj_*F with Rj_*G. The finite-ring constructible-origin theorem
lem-weil-pbc-finite-ring-constructible-derived-origin gives intrinsic constructibility.
The forward direction of lem-exc-comparison-tor-interval tests every pro-etale module
sheaf, including those with no etale origin, and gives the asserted Tor interval.
6. Monoidal comparison pullback and constant-section normalization identify the residue
tensors (lem-weil-pbc-ringed-topoi-derived-tensor-pullback). Exactness
lem-sf-comparison-pullback-exact preserves their interval. Both F and its residue
tensor are bounded below by Step 2, so
lem-sfb-projection-comparison-etale-proetale applies and gives precisely the displayed
square of adjunction projection maps. Constant inverse-image identifies its etale
endpoint with the normalized finiteConstantProjectionMap endpoint.
7. Naturality of the projection, tensor comparison, and direct-image mates gives
naturality in G. For two origins, thm-weil-pbc-site-comparison uniquely lifts e followed
by inverse e1. Full faithfulness forces these lifts to compose for three origins.
Their naturality squares prove origin independence, without any perfectness of kappa.
-/
theorem proEtale_open_residue_tor_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] [Invertible (l : k)]
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    @openResidueFixedTorBoundAssertion
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ (Padic.coefficientExtensionRing l E n)
        (Padic.finite_coefficientExtensionRing l E n hn) Equiv.ulift.symm)
      (openResidueModule (Padic.coefficientExtensionRing l E n)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
          (Padic.coefficientExtensionUniformizer l E))) U X j := by
  sorry

end AlgebraicGeometry.ProEtale
