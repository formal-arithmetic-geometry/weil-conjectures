/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteProperBaseChange
import WeilConjectures.AlgebraicGeometry.IntegralProperBaseChange
import WeilConjectures.SixFunctors.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.LocalizedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchangeTriangulated
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.FlatScalarTowerCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoExchange

/-! # Proper exchange on condensed generators along arbitrary base maps

Source: blueprint latest, sec-six-functors-basics/sk-thm-sfb-proper-base-change,
finite, integral and rational coefficient paragraphs; Stacks Tags 0DDE and 09C9
(blueprint: lem-zl-condensed-arbitrary-proper-generators).

The map is the specified unit--square--counit mate in the ordinary unbounded
module-object derived category. Only its bounded constructible finite-Tor inputs
are asserted to have invertible exchange. The base map need not be over `k`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper exchange on every constructible finite-Tor generator, for an arbitrary
scheme base map. The coefficient comparisons come from the point. In particular,
there is no `IsOver` hypothesis on `v` or on the first pullback projection.
Source: blueprint latest, sk-thm-sfb-proper-base-change, finite/integral/rational
paragraphs; Stacks Tags 0DDE and 09C9
(blueprint: lem-zl-condensed-arbitrary-proper-generators).

Proof plan:
1. Use lem-weil-pbc-profinite-point-pullback for canonical coefficient coherence for
   all scheme maps, and sk-prop-sfb-cartesian-coefficients for exact pullback.
   Properness and lem-weil-pbc-proper-base-change make both vertical maps qcqs.
2. For finite discrete coefficients use clause (2) of
   det-thm-sfb-proper-base-change-finite, including the zero ring and exponent zero.
3. For integral valuation-ring coefficients use clause (3) of
   det-thm-sfb-proper-base-change-integral on bounded constructible inputs, with
   ordinary pullback. Z_ell is the degree-one coefficient extension.
4. For a finite coefficient field rationalize the integral generators of
   det-lem-integral-models-generators. Exactness follows from
   lem-weil-pbc-continuous-integral-scalar-exact. Both localized push comparisons
   are invertible by lem-sfb-localized-direct-image-comparison: their inputs and
   exact pullbacks are bounded below, and their maps are qcqs. The equation of
   lem-sfb-scalar-geometric-exchange-rectangle then cancels all comparisons to give
   the specified field-coefficient exchange on these generators.
5. Apply lem-sfb-condensed-ambient-exchange-triangulated and the finite cone/shift
   generation in det-lem-integral-models-generators to obtain every field input.
6. For the finite-subextension-valued algebraic closure, first rationalize an
   integral generator. Both proper push comparisons are invertible by
   lem-weil-pbc-condensed-qbar-bounded-push on bounded-below inputs. Apply the same
   scalar/geometric rectangle and step 5. Exactness of the two scalar extensions
   follows from integral scalar exactness and lem-sfb-qlbar-flat; the associativity
   of lem-sfb-flat-scalar-tower-coherence identifies their composite with direct
   extension from the integral ring. The triangulated locus and the algebraic
   closure generation clause give every bounded constructible input.
7. Every coefficient allowed by hΛ is ring-isomorphic to a representative above.
   Use lem-sfb-condensed-coefficient-iso-exchange to transport invertibility of the
   actual mate. No extension to arbitrary objects of the localizing closure is used.
-/
theorem condensedAmbientExchange_isIso_arbitrary_proper_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {P Y Y' : Scheme.{u}}
    [P.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
    [IsSeparated (P ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : P ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q] (v : Y' ⟶ Y)
    (sq : ChosenCartesianSquare (pullback.fst q v) (pullback.snd q v) q v)
    (K : ConstantModelConstructibleFiniteTor Λ P) :
    IsIso ((condensedAmbientExchange Λ sq).app K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
