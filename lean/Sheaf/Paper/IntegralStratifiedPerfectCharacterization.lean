/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
public import Sheaf.Paper.ResidueLissePerfectLift
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Paper.DerivedComplete
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore

/-!
# Integral stratified perfect characterization

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and
Proposition 6.8.11(1),(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).

The perfect and finitely presented models below are actual constant-module
realizations extended to the completed coefficient ring. They are restricted to
strata and slice sites with their actual inverse-image coefficient action.

## Main statements

* `integralStratifiedPerfectCharacterization`: the three equivalent conditions.
* `integralStratifiedPerfectClosure`: shifts, cones, truncations and cohomology.
* `integralStratifiedPerfectDetailed`: comparison with the recorded detailed category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

/-- The ordinary realization N ↦ A_T ⊗_A N, using the normalized coefficient comparison.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralConstantModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{u + 1} A ⥤
      pbcModules T (pbcAdicCompletion T d) :=
  completedKoszulConstant T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite } ⋙
    pbcRestrict (pbcCompletedComparison T d).inv

/-- Exactness of the ordinary completed-constant realization.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: constant module sheafification is exact. The completed ring is flat over
constant A by lem-weil-pbc-completed-constant-sheaf-reduction, since d is Noetherian.
Thus tensoring with it preserves finite limits and colimits. Restriction along the
normalized coefficient isomorphism is an exact equivalence. -/
theorem integralConstantModule_exact (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (integralConstantModule T d) ∧
      PreservesFiniteColimits (integralConstantModule T d) := by
  sorry

/-- Additivity of completed-constant realization, inherited from its two factors.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
instance integralConstantModule_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : (integralConstantModule T d).Additive :=
  letI := (integralConstantModule_exact T d).1
  Functor.additive_of_preserves_binary_products _

/-- The derived realization P ↦ A_T ⊗^L_A P, obtained by localizing the exact
ordinary constant-module realization. On bounded finite projective complexes this
is its termwise tensor realization.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralConstantDerived (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : completedConstantDerived (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategory

/-- Restrict a derived object first to a stratum and then to a covering site object.
The slice coefficient sheaf is the restriction of the actual inverse-image ring.
Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 0997 and 0998
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralLocalDerived {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    completedConstantDerived (SheafOfModules.{u + 1}
      (((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)).over U)) :=
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U
    ((adicTowerPullback g R).obj K)

/-- Condition (ii): finite strata, on each a pro-etale covering sieve, and on each
cover member an actual perfect A-complex whose completed realization is K there.
IsPerfectRingComplex is the recorded bounded finite-projective notion.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralStratifiedPerfect (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  ∃ s : LocallyClosedStratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
            @DerivedCategory.IsPerfectRingComplex A _
              (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
              Nonempty (integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U K ≅
                integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U
                  ((integralConstantDerived T d).obj P))

/-- The constructible integral sheaf condition: finite strata and locally the ordinary
completed realization of a finitely presented A-module, including the zero module.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralStratifiedFinitelyPresented (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (F : pbcModules T (pbcAdicCompletion T d)) : Prop :=
  ∃ s : LocallyClosedStratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ N : ModuleCat.{u + 1} A, Module.FinitePresentation A N ∧
            Nonempty ((SheafOfModules.overFunctor _ U).obj
              ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj F) ≅
              (SheafOfModules.overFunctor _ U).obj
                ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj
                  ((integralConstantModule T d).obj N)))

/-- Condition (iii): boundedness and the stated finitely presented local models for
all cohomology sheaves. The finite stratification may depend on the cohomological degree.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralBoundedConstructibleCohomology (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  (∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    ∀ q : ℤ, IsIntegralStratifiedFinitelyPresented T d
      ((DerivedCategory.homologyFunctor (pbcModules T (pbcAdicCompletion T d)) q).obj K)

/-- The three descriptions are equivalent. Source: Bhatt--Scholze, Definition 6.5.1,
Proposition 6.6.11 and Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof, following the node step by step:

1. Fix the completed coefficient convention throughout. The completed-constant reduction lemma
gives flatness of A_T over the constant A-sheaf and A_T\otimes_A^L A/\varpi^n\simeq(A/\varpi^n)_T.
For a stratum immersion i:S\to T, inverse image is exact and preserves limits, hence
i^{-1}A_T=A_S; for a site object U\to S, slice restriction has the same property by the
localization description. In particular these restrictions preserve finite reductions and their
normalization maps. To check completeness, use the quotient-tower completion unit furnished by the
constant-completion equivalence. Exact countable products compute derived products termwise, and
the strict-tower Roos triangle computes its derived limit. Exact restriction preserving products
therefore preserves this unit and its cone. The finite-stratum detection lemma, followed by
covering detection of zero sheaves, shows that the cone vanishes on T if and only if it vanishes
on all chosen stratum covers. Thus intrinsic completeness restricts to strata and covers and is
detected on a finite stratification. This argument uses the actual coefficient isomorphism for
immersions and slices, not scalar extension along an arbitrary scheme morphism.
Uses: lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-proetale-immersion-limit-
preservation, lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-constant-completion-
equivalence, lem-weil-proetale-countable-products-exact, lem-weil-derived-countable-products-core,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-noetherian-stratum-detection.

2. For a bounded finite-projective A-complex P, its completed constant realization is A_U\otimes_A
P termwise. Its finite reductions are the constant complexes P\otimes_A A/\varpi^n by the
completed-constant reduction lemma. In each degree the finite-projective module is a summand of
A^r; the transition maps on the corresponding constant sheaves are sectionwise surjective by the
constant-module section lemma. On products of this tower, 1-s is sectionwise surjective: given
(y_n), choose x_1 and recursively lift x_n-y_n to x_{n+1}, so x_n-q(x_{n+1})=y_n. Its kernel is
the inverse limit. The limit of a finite-projective summand is the same summand of A_U^r. The Roos
triangle therefore identifies the quotient completion unit with an isomorphism onto the original
realized complex. Such a complex is intrinsically complete. A finite stratification with perfect
local models has globally bounded cohomology and globally bounded reductions: each stratum is
quasi-compact, so the covering axiom of the pro-etale site allows finitely many quasi-compact
pieces of the trivializing cover to cover it; take the smallest and largest term degrees of their
finitely many models. The finite-stratum detection lemma detects vanishing outside these bounds.
Completeness also follows from step 1.
Uses: lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-constant-module-section-
properties, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-constant-completion-
equivalence, lem-weil-pbc-noetherian-stratum-detection, def-weil-pbc-proetale-site.

3. Assume (i). The uniform tower definition gives local complexes in a fixed term interval
[d_0,d_1], and every cohomology sheaf of K_1 is finite lisse on its finite stratification. Uniform
boundedness of the derived reductions requires a separate check: for every n\geq1, over the DVR A,
[A\xrightarrow{\varpi^n}A] in degrees [-1,0] resolves A/\varpi^n. Flatness and finite reduction in
the completed-constant reduction lemma therefore give the flat resolution
[A_T\xrightarrow{\varpi^n}A_T] of (A/\varpi^n)_T. Tensoring a local complex from the uniform tower
definition with this resolution has terms only in [d_0-1,d_1]. Its quasi-isomorphism with K_n on
the chosen covers, and the finite-stratum detection of step 1, give that same global cohomological
interval independently of n. In particular K_1 is bounded with intrinsically constructible
cohomology. Finite-ring derived origin gives a bounded constructible etale complex L_1 with
\nu_T^*L_1\simeq K_1; one may use the existing compatible witness, since bounded-below full
faithfulness identifies it with this origin. By the definition of etale constructibility choose a
finite stratification on which all the finitely many nonzero cohomology sheaves of L_1 are finite
locally constant. A common refinement is obtained by intersecting the finitely many locally closed
partitions and using their fibre-product immersions. Comparison-pullback identifies its
restriction to every new stratum with the corresponding restriction of K_1. Apply finite-ring
derived local constancy on each stratum to L_1. Since A/\varpi is a field, its bounded finite-
module constant models are perfect: split cycles and boundaries as vector spaces to replace the
complex by its finitely many finite-dimensional cohomology spaces in their degrees. Step 1 makes K
intrinsically complete on every stratum. The coefficient ring is adically complete: for a
compatible family in A/\varpi^n, choose representatives x_n\in A. Compatibility gives
x_{n+1}-x_n\in\varpi^nA, so |x_m-x_n|_E\leq|\varpi|_E^n for m\geq n. Completeness of E gives a
limit x in its closed unit ball A; each closed ball x_n+\varpi^nA contains that limit. Thus x has
the prescribed residues, and \bigcap_n\varpi^nA=0 gives uniqueness. This verifies the extra adic-
completeness hypothesis of the lifting lemma. The residue-lisse perfect-lifting lemma now gives
pro-etale locally a perfect A-complex on each stratum. This proves (ii). No claim is made that a
general finite-ring bounded complex is perfect; the residue field is essential here.
Uses: def-weil-pbc-bounded-constructible-complete, def-weil-pbc-bounded-constructible-tower, prop-
weil-pbc-site-comparison-finite-level, lem-weil-pbc-finite-ring-constructible-derived-origin, lem-
weil-pbc-finite-ring-derived-local-constancy, lem-weil-l-adic-extension-integers-dvr, lem-weil-
pbc-residue-lisse-perfect-lift, lem-weil-pbc-comparison-pullback, lem-weil-l-adic-extension-
complete, lem-weil-l-adic-extension-absolute-value, lem-weil-pbc-completed-constant-sheaf-
reduction, lem-weil-pbc-noetherian-stratum-detection, def-weil-pbc-etale-constructible-sheaf, thm-
weil-pbc-site-comparison.

4. Assume (ii). Steps 1 and 2 give intrinsic completeness and a common cohomological interval for
all reductions K_n. Their restrictions to the given strata are constant perfect
(A/\varpi^n)-complexes locally, so every finite-level cohomology sheaf is finite lisse there. The
quotient tower has the strict realization and normalization cocycle of the coefficient-datum
definition. Normalized constructible local effectivity supplies exactly the common local models
required by the uniform tower definition. Finite-ring derived origin supplies L_n\in
D^+(T_{\mathrm{et}},A/\varpi^n) and \alpha_n:\nu_T^*L_n\simeq K_n. Pullback commutes with
coefficient tensor, so the source L_{n+1}\otimes^L_{A/\varpi^{n+1}}A/\varpi^n pulls back to K_n.
Exact finite-level comparison reflects zero cohomology sheaves, by its sheaf unit; therefore this
source is bounded before bounded-below full faithfulness is applied. Lift
\alpha_n^{-1}\rho_n(\alpha_{n+1}\otimes^L A/\varpi^n) uniquely by full faithfulness to \beta_n.
Its inverse also lifts, so \beta_n is an isomorphism. Faithfulness turns the quotient-cocycle
equalities after pullback into equalities of the lifted maps. These are compatible etale-origin
witnesses as required, not unrelated levelwise origins. All conditions of (i) hold.
Uses: def-weil-pbc-adic-coefficient-datum, lem-weil-pbc-normalized-constructible-local-
effectivity, lem-weil-pbc-finite-ring-constructible-derived-origin, lem-weil-pbc-ringed-topoi-
derived-tensor-pullback, prop-weil-pbc-site-comparison-finite-level, thm-weil-pbc-site-comparison,
def-weil-pbc-bounded-constructible-complete.

5. Assume (ii). On a perfect local model P, flatness over the constant A-sheaf identifies \mathcal
H^q(A_U\otimes_A P) with A_U\otimes_A H^q(P). The kernels of the differentials in the finite-
projective terms of P are finitely generated by Noetherian submodule finiteness, and their
quotient cohomology modules are finitely generated. They are finitely presented over A by the
Noetherian finite-presentation lemma. Step 2 supplies the global finite cohomological bound. These
descriptions on the same strata are precisely (iii).
Uses: lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-noetherian-submodule-finite,
lem-sc-noetherian-finite-module-finite-presentation, lem-weil-l-adic-extension-integers-dvr.

6. Let C be any cohomology sheaf allowed by (iii). On a stratum cover it is A_U\otimes_A N with N
finitely presented. Choose a surjection A^r\to N. Its kernel is finitely generated by Noetherian
submodule finiteness and torsion-free as a submodule of A^r. The DVR torsion-free module lemma
makes it finite free. Thus 0\to A^s\to A^r\to N\to0 gives a perfect A-complex in degrees [-1,0].
Flatness of A_U over the constant A-sheaf realizes this resolution with cohomology exactly C in
degree zero. This proves (ii) for C[0], with the same two term bounds on all strata and covers;
step 4 proves (i) for C[0]. This is a resolution argument, not an additional node restating the
degree-zero clause.
Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-noetherian-submodule-finite, lem-sc-
dvr-fg-torsionfree-free, lem-weil-pbc-completed-constant-sheaf-reduction.

7. Assume (iii), with \mathcal H^q(K)=0 outside [a,b]. Step 6 puts each \mathcal H^q(K)[-q] in
(i). Start with \tau^{\leq a-1}K=0. For q=a,\ldots,b, the standard truncation triangle has
vertices \tau^{\leq q-1}K, \tau^{\leq q}K, and \mathcal H^q(K)[-q]. Inductively the outer vertices
belong to (i), and the uniform-complete triangulated lemma puts the middle vertex in (i). At q=b
the middle vertex is K. This proves (iii) implies (i), completing all three equivalences. The
induction is finite; it does not commute truncation with finite coefficient reduction.
Uses: def-sbc-standard-tstructure-derived-category, lem-sf-derived-truncation-triangle, lem-weil-
pbc-uniform-complete-triangulated. -/
theorem integralStratifiedPerfectCharacterization
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤)))
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))) :
    (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K) ∧
    (IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K ↔
      IsIntegralBoundedConstructibleCohomology T (pbcIntegralDatum l E) K) := by
  sorry

/-- Closure under all shifts, ambient cones, standard truncations and cohomology in
degree zero. Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: uniform complete objects form a triangulated subcategory. By the characterization,
standard truncations are bounded and retain the same allowed cohomology sheaves, with
some replaced by zero; likewise cohomology placed in degree zero. Apply (iii) ⇒ (i).
This uses no assertion that truncation commutes with finite reduction. -/
theorem integralStratifiedPerfectClosure
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) :
    (∀ K, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K →
      ∀ n : ℤ, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((shiftFunctor _ n).obj K)) ∧
    (∀ Δ : Triangle
      (DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))),
      Δ ∈ distTriang _ → PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) Δ.obj₁ →
        PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) Δ.obj₂ →
        PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) Δ.obj₃) ∧
    (∀ K, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K → ∀ n : ℤ,
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (∀ K, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K → ∀ q : ℤ,
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  sorry

/-- The quotient coefficient identification induced by the canonical valuation-ring lift.
The normalization on representatives determines the equivalence uniquely. The source
uses the recorded valuation ring lifted to the small site's coefficient universe.
Source: blueprint coefficient conventions, order 411; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: ULift.down is a ring equivalence from the recorded lifted valuation ring to the
original valuation ring. It sends the recorded lifted uniformizer to the original
uniformizer, and hence identifies their principal ideals and every positive power.
Descend this equivalence to the quotients and lift its target. Surjectivity of the
quotient map proves uniqueness from the displayed representative formula. -/
theorem integralCoefficientULift_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ∃! e : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ x : PbcIntegralRing l E,
        e (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down) := by
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E :=
    ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E (n + 1) =
      Ideal.map e.toRingHom ((pbcIntegralDatum l E).ideal ^ (n + 1)) := by
    simp [pbcIntegralDatum, Padic.coefficientExtensionIdeal, Ideal.map_pow,
      Ideal.map_span, Set.image_singleton, e, pbcUniformizer]
    rfl
  let q := Ideal.quotientEquiv _ _ e hI
  refine ⟨q.trans ULift.ringEquiv.symm, ?_, ?_⟩
  · intro x
    change ULift.up (q (Ideal.Quotient.mk _ x)) = _
    rw [Ideal.quotientEquiv_mk]
    rfl
  · intro e' he'
    apply RingEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (he' x).trans (by
      change ULift.up (Ideal.Quotient.mk _ x.down) =
        ULift.up (q (Ideal.Quotient.mk _ x))
      rw [Ideal.quotientEquiv_mk]
      rfl)

/-- The uniquely normalized quotient equivalence, not an arbitrary field identification.
Source: blueprint coefficient conventions, order 411; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralCoefficientULift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  (integralCoefficientULift_exists l E n).exists.choose

/-- The finite-level coefficient isomorphism: undo the normalized functions-sheaf
presentation, apply the quotient lift and forget commutativity.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralDetailedLevelComparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (adicLisseForget T).obj
        ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)) ≅
      WeilConjectures.integralCoefficientSheaf l E T n :=
  (adicLisseForget T).mapIso
    ((pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
        (integralCoefficientULift l E n).toCommRingCatIso)

/-- The unique completed coefficient comparison compatible with every finite projection.
This keeps the detailed definition's actual ring and positive reduction functors.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: the normalized finite-level comparisons commute with transitions, as can be
checked on residue representatives. Apply the limit universal property. Forgetting
commutativity preserves limits, so both rings are limits of the same quotient system.
The projection identities determine a unique isomorphism. -/
theorem integralDetailedCoefficientComparison_exists
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃! e : (adicLisseForget T).obj
        (pbcAdicCompletion T (pbcIntegralDatum l E)) ≅
          WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T,
      ∀ n : ℕ,
        e.hom ≫ limit.π (WeilConjectures.integralCoefficientSheafSystem l E T) (op n) =
          (adicLisseForget T).map
              (pbcAdicProjection T (pbcIntegralDatum l E) n) ≫
            (integralDetailedLevelComparison T l E n).hom := by
  let d := pbcIntegralDatum l E
  let F := adicLisseForget T
  let C := constantSheaf (ProEt.topology T) CommRingCat.{u + 1}
  have hq (n : ℕ) (x : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ x) =
        ULift.up (Ideal.Quotient.mk _ x.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec x
  have htrans (n : ℕ) :
      CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ≫
        (integralCoefficientULift l E n).toCommRingCatIso.hom =
      (integralCoefficientULift l E (n + 1)).toCommRingCatIso.hom ≫
        CommRingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom).comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              ULift.ringEquiv.toRingHom)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change integralCoefficientULift l E n
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1) (Ideal.Quotient.mk _ x)) = _
    change integralCoefficientULift l E n (Ideal.Quotient.mk _ x) = _
    rw [hq]
    change ULift.up (Ideal.Quotient.mk _ x.down) =
      ULift.up ((Padic.coefficientExtensionTransition l E (n + 1))
        ((integralCoefficientULift l E (n + 1) (Ideal.Quotient.mk _ x)).down))
    rw [hq]
    rfl
  let c : adicLisseRingSystem T d.ideal ⋙ F ⟶
      WeilConjectures.integralCoefficientSheafSystem l E T :=
    NatTrans.ofOpSequence
      (fun n ↦ F.map (C.map (integralCoefficientULift l E n).toCommRingCatIso.hom))
      (by
        intro n
        dsimp only [Functor.comp_map]
        simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
          WeilConjectures.integralCoefficientSheafSystem,
          WeilConjectures.integralCoefficientSheafTransition]
        change F.map (C.map _) ≫ F.map (C.map _) =
          F.map (C.map _) ≫ F.map (C.map _)
        simp only [← F.map_comp, ← C.map_comp, htrans])
  have (n : ℕᵒᵖ) : IsIso (c.app n) := by
    change IsIso (F.map (C.map (integralCoefficientULift l E n.unop).toCommRingCatIso.hom))
    infer_instance
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have : PreservesLimit (pbcAdicRings T d) F := by
    have : PreservesLimit (pbcAdicRings T d)
        (F ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}) :=
      inferInstanceAs (PreservesLimit (pbcAdicRings T d)
        (sheafToPresheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
          (Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat.{u + 1} RingCat.{u + 1}).obj
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
    exact preservesLimit_of_reflects_of_preserves F
      (sheafToPresheaf (ProEt.topology T) RingCat.{u + 1})
  let w := Functor.isoWhiskerRight (pbcConstantSystemComparison T d).symm F ≪≫ asIso c
  let e := preservesLimitIso F (pbcAdicRings T d) ≪≫ HasLimit.isoOfNatIso w
  refine ⟨e, ?_, ?_⟩
  · intro n
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl
  · intro e' he'
    apply Iso.ext
    apply limit.hom_ext
    intro n
    change e'.hom ≫ limit.π _ n = e.hom ≫ limit.π _ n
    rw [he' n.unop]
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl

/-- Canonical ring comparison, chosen from its unique projection normalization.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralDetailedCoefficientComparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (integralDetailedCoefficientComparison_exists T l E).exists.choose

/-- Scalar restriction along this canonical ring isomorphism is exact.
Source: Bhatt--Scholze, Section 6.5; Stacks Tag 03DA
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: restriction changes only the scalar action. Restriction along the inverse
is its inverse equivalence. Finite limits and colimits are unchanged on underlying
additive sheaves, and therefore preserved. -/
theorem integralDetailedCoefficientRestriction_exact
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom) := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom
  let R := (adicLisseForget T).obj (pbcAdicCompletion T (pbcIntegralDatum l E))
  let B := WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} B))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} B))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)⟩

/-- Transport the detailed category along the canonical coefficient isomorphism.
The valuation ring is lifted to the small site's coefficient universe u+1. The
finite extension E itself retains the recorded coefficient convention E : Type u.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralDetailedTransport
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      DerivedCategory (pbcModules T
        (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  letI := HasDerivedCategory.standard
    (WeilConjectures.scalarReductionSource.{u, u} l E T)
  letI := (integralDetailedCoefficientRestriction_exact T l E).1
  letI := (integralDetailedCoefficientRestriction_exact T l E).2
  (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom).mapDerivedCategory

/-- The same conditions describe precisely the detailed integral category under
its own coefficient hypotheses. The comparison is fixed by all quotient projections,
so it compares the same completed ring and reduction functors.
Source: Bhatt--Scholze, Definition 6.5.1 and Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof (step 8 of the node): For the detailed integral notation, use it only under its own
coefficient hypotheses and with the same completed ring and reduction functors. Membership in (i)
implies levelwise finite-torsion constructibility and the uniform interval, hence the reduction
conditions of the detailed definition. Intrinsic completeness is the quotient completion condition
by the constant-completion equivalence, and its Roos triangle supplies the completeness condition
of the detailed definition. Conversely a detailed object has intrinsically constructible finite-
level cohomology and the stipulated common interval. Its completeness Roos triangle identifies its
underlying object with the quotient derived limit. The latter is the Koszul completion object and
is intrinsically complete by the completion-reflector lemma; completeness is invariant under
isomorphism. This argument only needs the object identification and does not assert uniqueness of
a lift of its projection maps. Normalized constructible local effectivity gives the required
uniform tower models, and the full-faithfulness lifting argument in step 4 gives compatible etale
witnesses. Thus it belongs to (i). No equality between the constant and completed ambient module
categories is used.
Uses: def-weil-derived-complete-integral-detailed, def-weil-derived-complete, def-weil-finite-
torsion-constructibility, def-weil-pbc-bounded-constructible-complete, lem-weil-pbc-constant-
completion-equivalence, lem-weil-pbc-ringed-koszul-completion-reflector, lem-weil-pbc-normalized-
constructible-local-effectivity, thm-weil-pbc-site-comparison, lem-weil-pbc-ringed-topoi-derived-
tensor-pullback, prop-weil-pbc-site-comparison-finite-level. -/
theorem integralStratifiedPerfectDetailed
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian T] (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hinv : IsUnit (l : Γ(T, ⊤)))
    (K : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T)) :
    WeilConjectures.sfIntegralConstructible l E T K ↔
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((integralDetailedTransport T l E).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
