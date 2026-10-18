/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion

/-!
# Constructibility of all integral reductions from the first

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion/sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Derived completeness, constructibility of every positive reduction and a common
finite cohomological interval. The reduction index n denotes the exponent n+1.
There is no Tor-amplitude condition and no boundedness requirement on K itself.
The predicate is intrinsic to X and E; the global convention l != p has no role in it.
Source: Weil blueprint, order 1459, and the final paragraph of
sk-prop-integral-criterion-reductions
(blueprint: det-prop-integral-criterion-reductions). -/
def continuousIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) :=
  fun K ↦ IsDerivedComplete l E X K ∧
    (∀ n : ℕ, constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1))
      X ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
    ∃ r s : ℤ, r ≤ s ∧ ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K))

/-- The full subcategory with the inherited ambient derived morphisms.
Source: Weil blueprint, order 1459
(blueprint: det-prop-integral-criterion-reductions). -/
abbrev ContinuousIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) := (continuousIntegralConstructible l E X).FullSubcategory



/-- The projection-normalized comparison is independent of all auxiliary finite-set
representations and limit-cone witnesses. SfbIntegralComparison retains the unit
and all reduction equations, not just existence of an isomorphism.
Source: blueprint integral-limit clause 3; integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: existence is sfb_integral_coefficient_limit. For uniqueness, the finite-label
representation is unique: on a singleton both sheaves are terminal, and naturality
with every singleton-to-finite-set inclusion fixes each constant label; sheafification
then fixes the whole natural transformation. For each cone witness the composite
j followed by its nth projection is the specified quotient on every integer, so
changing the cone changes none of these maps. The adjunction-mate normalization
therefore gives the same nth projection for both comparisons on every profinite
test object and continuous integer-valued function. The adjunction and Yoneda
identify the maps; finally the limit projections jointly distinguish them. -/
theorem integralLimitAbComparison_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃! e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X,
      SfbIntegralComparison l E X e := by
  sorry

/-- The unique integral-limit comparison with the published adjunction-mate and
finite-projection normalization. No finite representation or equivalence is selected
from a bare existence statement.
Source: blueprint integral-limit clause 3; integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralLimitAbComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  (integralLimitAbComparison_existsUnique l E X).exists.choose

/-- The coefficient presentations have the same underlying abelian sheaves.
Source: blueprint integral-limit clause 3 and integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the section-ring construction keeps the additive group and restriction maps
of the internal ring. On the point the two continuous-function constructions have
identical sections and restrictions: the extending absolute value is the spectral
norm, hence defines the same topology. Presheaf extensionality and proof irrelevance
identify these sheaves, and applying the same point inverse image preserves equality.
The completed commutative ring sheaf retains the ring data of the completed ring
sheaf; forgetting its commutativity and multiplication keeps exactly its additive
groups and restrictions. Sheaf extensionality gives the second equality. -/
theorem integralSectionAbIdentifications (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)) =
        (coefficientRing X (sfbCondensedIntegers l E)).X ∧
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X) =
        sfbCompletedIntegersAb l E X := by
  sorry

/-- Reconstructing section rings retains the unique projection-normalized coefficient
comparison. After the endpoint identifications, forgetting to abelian sheaves fixes
the entire underlying additive map.
Source: blueprint integral-limit clause 3 and integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the spectral absolute value defining DerivedNakayama.integerRing is the
spectral norm defining sfbCondensedIntegers, so the continuous-function sheaves and
their point pullbacks agree. The chosen abelian comparison is a monoid homomorphism
in both directions by sfb_integral_coefficient_limit. Evaluating its multiplication
and unit identities reconstructs a commutative-ring isomorphism on sections.
Naturality is unchanged. Forgetting to abelian sheaves is faithful, so the fixed
underlying comparison determines this ring isomorphism uniquely. -/
theorem integralSectionRingIso_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃! e : CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (AdicCompletion.ring l E X) ≅
        WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X,
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom =
          eqToHom (integralSectionAbIdentifications l E X).1 ≫
            (integralLimitAbComparison l E X).hom ≫
              eqToHom (integralSectionAbIdentifications l E X).2.symm := by
  sorry

/-- The ring comparison fixed by the published finite-projection normalization.
Source: blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionRingIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  (integralSectionRingIso_existsUnique l E X).exists.choose

/-- The actual section-action functor, followed by scalar transport along the inverse
of the specified coefficient isomorphism. Neither functor is chosen by existence.
Source: Stacks 00YV; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionFunctor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    AdicCompletion.Modules l E X ⥤ WeilConjectures.scalarReductionSource.{u, u} l E X :=
  (CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)).functor ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralSectionRingIso l E X).inv)

/-- The prescribed section-action comparison is an additive equivalence.
Source: Stacks 00YV, 03DA; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: sectionModuleEquivalence is the existing exact equivalence with the same
underlying abelian sheaves. Restriction along the inverse coefficient isomorphism
has inverse restriction along its forward map. The unit and counit are the identity
on sections, with the two scalar actions identified by the inverse equations.
Both functors preserve addition on every section, so their composite is additive. -/
theorem integralSectionFunctor_properties (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (integralSectionFunctor l E X).Additive ∧
      (integralSectionFunctor l E X).IsEquivalence := by
  sorry

/-- Additivity of the actual section-action functor.
Source: blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
instance integralSectionFunctor_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : (integralSectionFunctor l E X).Additive :=
  (integralSectionFunctor_properties l E X).1

/-- Equivalence of the actual section-action functor.
Source: blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
instance integralSectionFunctor_isEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : (integralSectionFunctor l E X).IsEquivalence :=
  (integralSectionFunctor_properties l E X).2

/-- Localization of the fixed section-action equivalence on unbounded complexes.
Its forward functor is the localization of integralSectionFunctor, with Mathlib's
canonical localization comparison on every complex.
Source: Stacks 05RU; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionDerivedEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    DerivedCategory (AdicCompletion.Modules l E X) ≌
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E X) :=
  letI : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
    (integralSectionFunctor_properties l E X).1
  (integralSectionFunctor l E X).asEquivalence.mapDerivedCategory

/-- The continuous predicate is the existing integral predicate under the canonical
coefficient and section-action comparison, rather than an unrelated new notion.
Source: blueprint integral-criterion final sentence, proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the finite projections of integralSectionRingIso are the specified quotient
maps by its underlying integral-limit normalization. On a K-flat representative,
the section-action equivalence identifies tensoring with each quotient with the
recorded scalarReductionDerivedExtension; this also identifies the quotient units
and transitions. Exact equivalences preserve products and the augmented Roos
triangle, so IsDerivedComplete agrees with IsSfDerivedComplete. At each positive
finite level the continuous ring is constant. Finite constant local models agree
with locally constant finite modules: finite presentation over a finite ring gives
a finite module, and a finite module has a finite presentation. The Noetherian
finite stratifications agree. Finally homology is preserved by the exact
equivalence, and support in [r,s] means precisely vanishing outside [r,s]. These
identifications give both implications, including the same uniform interval. -/
theorem continuousIntegralConstructible_iff_sfIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    continuousIntegralConstructible l E X K ↔
      WeilConjectures.sfIntegralConstructible l E X
        ((integralSectionDerivedEquivalence l E X).functor.obj K) := by
  sorry

/-- First reduction versus all positive reductions with a uniform cohomological interval.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion/sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).

Proof:
1. For the reverse implication take n=0, which denotes exponent 1.
2. The finite extension DVR and finite quotient results give finite coefficient rings.
   Their continuous condensed sheaves are constant, and finitely presented modules over
   them are precisely finite modules. Thus the two finite constructibility conventions
   agree (sk-def-sfb-constructible, def-weil-proetale-constructible-sheaf,
   sk-def-sfb-pullback-from-point, det-prop-sfb-qlbar-colimit-x-integral-limit).
3. Cancellation of the uniformizer gives the short exact coefficient sequence
   0 -> R_(n-1) -> R_n -> R_1 -> 0 for n>1, with its R_n-linear maps
   (det-pe-derived-nakayama-resolution, def-weil-sheaf-of-modules-category).
4. Choose a flat-term K-flat resolution of K (lem-pc-kflat-resolution). Termwise
   tensor preserves that sequence (def-pc-flat-sheaf-modules). Its short-exact-sequence
   triangle (lem-weil-pbc-complex-ses-triangle) computes the reductions in D(R_n)
   by lem-pur-derived-change-of-rings, with the outer terms restricted from their
   quotient coefficient rings. No boundedness of the original K is required.
5. Exact restriction of scalars leaves the underlying sheaves and finite local models
   unchanged, so preserves constructibility and cohomological bounds
   (def-pc-sheaf-restrict-scalars, def-weil-proetale-constructible-sheaf).
6. Fix r<=s bounding K_1. Induction on the positive exponent and closure under
   distinguished triangles (lem-weil-proetale-dbc-triangulated) prove constructibility.
7. The long exact cohomology sequence (lem-sf-derived-homology-long-exact) has zero
   outer terms outside [r,s], hence zero middle term. This is the same interval at
   every level. Completeness is retained as in the source, though steps 1--7 do not use it.
8. For the integral interpretation, the pulled-back continuous integer ring is the
   completed finite coefficient tower (det-prop-sfb-qlbar-colimit-x-integral-limit).
   The canonical completion isomorphism identifies its augmented Roos triangle with
   the completeness triangle (sk-def-pe-derived-completion, def-weil-derived-limit,
   def-weil-derived-complete). Finite constructibility agrees by step 2, and support
   in [r,s] is exactly vanishing outside it (def-weil-cohomological-support).
   Thus the all-reductions condition is precisely the remaining integral condition
   of def-weil-derived-complete-integral-detailed. No Tor-amplitude is inserted. -/
theorem integral_reductions_constructible_iff (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : IsDerivedComplete l E X K) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ↔
      (∀ n : ℕ, constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1))
        X ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧ ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X n).obj K)) := by
  sorry

/-- The first-reduction criterion describes the bounded constructible complete integral
category in the same continuous coefficient presentation.
Source: blueprint main-20261015, final sentence of sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).
Proof: apply integral_reductions_constructible_iff to the assumed complete K, and unfold
continuousIntegralConstructible. Its first conjunct is the given completeness, and its
remaining conjuncts are exactly all positive constructible reductions and the common
interval. The coefficient, completeness and support identifications are step 8 of the
preceding proof plan; in the original global setting this applies when l != p. -/
theorem continuousIntegralConstructible_iff_first_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : IsDerivedComplete l E X K) :
    continuousIntegralConstructible l E X K ↔
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  sorry


/-- The first-reduction criterion in the existing sectionwise integral category.
Source: blueprint integral-criterion final sentence
(blueprint: det-prop-integral-criterion-reductions).
Proof: combine continuousIntegralConstructible_iff_sfIntegralConstructible with
continuousIntegralConstructible_iff_first_reduction. Both comparisons use the same
specified coefficient transport and the original complete object K. -/
theorem sfIntegralConstructible_iff_first_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : IsDerivedComplete l E X K) :
    WeilConjectures.sfIntegralConstructible l E X
        ((integralSectionDerivedEquivalence l E X).functor.obj K) ↔
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
