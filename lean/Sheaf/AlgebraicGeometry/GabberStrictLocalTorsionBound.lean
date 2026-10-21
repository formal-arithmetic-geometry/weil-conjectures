/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.TraceFormula.GabberNearbyCycleDimensionBound
import Sheaf.TraceFormula.OrientedPointCohomology

/-!
# Gabber's strict-local torsion cohomological bound

Source: Illusie, Around the Thom-Sebastiani theorem, Corollary 1.15 with the
hypotheses of Theorem 1.14, printed pp. 15–16
(blueprint: lem-trf-gabber-strict-local-torsion-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- On strict localizations, higher direct images of arbitrary torsion module sheaves
vanish above twice a uniform bound on the dimensions of the scheme-theoretic fibres.

Source: Illusie, Around the Thom-Sebastiani theorem, Corollary 1.15 and Theorem 1.14,
printed pp. 15–16 (blueprint: lem-trf-gabber-strict-local-torsion-bound).

Proof:
1. Put T = X_(x), B = S_(f(x)), j : T → X and h = f_(x). The strict localizations
   are affine (def-weil-pbc-strict-henselization-limit). An affine scheme is separated
   (lem-weil-pbc-affine-source-morphism-separated), and a map from an affine scheme to
   an affine separated scheme is affine
   (lem-weil-pbc-affine-source-separated-target-affine-morphism), hence qcqs
   (lem-weil-pbc-affine-morphism-permanence). Forget coefficients to the finite ring
   A = Z/m. For both A and Λ, lem-sbc-higher-direct-image-forget-comparison identifies
   the underlying abelian higher images, so it suffices to prove the assertion for A.
2. First take G = j^*F for a sheaf F on X. For q > 2N,
   lem-trf-gabber-nearby-cycle-dimension-bound kills H^q RΨ_f(F[0]). The point formula
   lem-trf-oriented-point-cohomology, with second map the identity of S, kills the
   cohomology of T ×_B S_(t₀) for every specialization S_(t₀) → B. Point inverse image
   is exact and commutes with forgetting (lem-pe-constant-left-module-inverse-image).
3. For a geometric point t of B and its image t₀ in S, the closed point of B maps
   to f(x) (lem-weil-pbc-strict-henselization-functoriality). An affine chart of S
   containing f(x) therefore contains the image of all B: an open of a local affine
   containing its closed point is the whole scheme. The chart ring map is ind-etale
   by lem-weil-pbc-strict-henselization-affine-chart-ind-etale. Thus
   lem-trf-ind-etale-strict-local-invariance gives e : B_(t) ≅ S_(t₀) over S.
   Compose e⁻¹ with B_(t) → B to obtain the specialization in step 2. The pullback
   universal property (def-pc-fibre-product) identifies its tube with T ×_B B_(t).
4. Apply prop-weil-pbc-strict-henselization-stalk-formula to the qcqs h and the
   torsion underlying abelian sheaf. The groups in step 3 compute all stalks of its
   higher image. Use lem-pe-left-module-derived-evaluation-forget to identify module
   cohomology with abelian cohomology, and lem-pe-constant-left-module-inverse-image
   for inverse images. By lem-sbc-higher-direct-image-forget-comparison and
   lemma-weil-pbc-geometric-stalk-conservative, the module higher image is zero.
5. The affine T is qcqs (lem-weil-pbc-affine-scheme-qcqs). Over the finite ring A,
   lem-weil-pbc-module-sheaf-colimit-constructible expresses an arbitrary sheaf as
   a filtered colimit of constructible sheaves. The qcqs h satisfies
   lem-sbc-higher-direct-image-large-filtered-colimit. It remains to kill each term.
6. Affine pointed neighbourhoods and their transition maps are qcqs and affine by
   the geometry in step 1. Reindex the strict-local limit over a directed set using
   lem-weil-pbc-cofiltered-limit-directed-reindex. By
   lem-weil-pbc-constructible-module-limit-descent, a constructible C on T descends
   to C_U on an affine pointed etale neighbourhood u : U → X with a : T → U and
   a ≫ u = j. Only the constructible sheaf, not an arbitrary sheaf, descends.
7. In P = T ×_X U, the section (1,a) of v : P → T is clopen. Indeed u is separated
   (lem-weil-pbc-affine-source-morphism-separated); its base change v is separated
   and etale (lem-weil-pbc-separated-base-change, lem-weil-pbc-etale-scheme-base-change),
   so lem-weil-pbc-etale-section-clopen-immersion applies. Write P = T ⨿ P₁.
8. For F = u_!C_U, lem-weil-pbc-etale-shriek-base-change-modules identifies j^*F
   with v_!b^*C_U, b : P → U. The sum-extension formula
   def-weil-pbc-etale-sum-extension splits this as C ⊕ E: on an etale test object,
   separate lifts into the two clopen parts and glue over their disjoint open cover.
   Inclusion and projection of the first summand make C a retract of j^*F.
9. Higher direct image preserves this retraction; step 4 kills its middle object,
   so the identity of R^q h_*C is zero. Step 5 gives the assertion for every A-sheaf,
   since a colimit of zero objects is zero. Step 1 restores Λ coefficients because
   forgetting the module structure reflects zero objects.
-/
theorem gabber_strictLocal_torsion_bound
    {X S : Scheme.{u}} (m : ℕ) (hm : 1 ≤ m)
    (Λ : Type (u + 1)) [CommRing Λ] (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    (f : X ⟶ S) [LocallyOfFiniteType f] (N : ℕ)
    (hN : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (N : WithBot ℕ∞))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : Sheaf (Scheme.strictHenselizationScheme x).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : 2 * (N : ℤ) < q) :
    IsZero
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (Scheme.strictHenselizationScheme (x ≫ f)).smallEtaleTopology
          (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
          (Scheme.strictHenselizationMap f x)).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (Scheme.strictHenselizationScheme x).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj G))) := by
  sorry

end AlgebraicGeometry.Etale
