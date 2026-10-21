/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralReductionTowerWellDefined
import Sheaf.CategoryTheory.Triangulated.DerivedLimitMorphism

import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Paper.DerivedComplete
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Mathlib.Topology.Constructible
import Sheaf.Paper.SfDerivedDirectImage
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Integral compact-support constructibility

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0GL0
(blueprint: lem-sf-integral-compact-support-constructible).

The finite terms use the chosen compactification. The quotient transitions are the
scalar-extension adjuncts of the reduction units followed by the normalized
compact-support coefficient comparisons. Derived limits are properties of arbitrary
objects, expressed by their Roos triangles.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Positive coefficient levels are finite. Source: blueprint coefficient extension;
Bhatt--Scholze, Section 6.7 (blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable instance sfCompactSupportCoefficientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Restriction from exponent n+2 to exponent n+1 along the specified quotient map.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable abbrev sfCompactSupportFiniteRestriction (T : Scheme.{u}) (n : ℕ) :
    scalarReductionTarget.{u, u} l E T n ⥤ scalarReductionTarget.{u, u} l E T (n + 1) :=
  proEtaleCoefficientRestrictScalars T (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finite quotient restriction is left exact. Source: Stacks Tag 03DA
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable instance sfCompactSupportFiniteRestrictionLimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (sfCompactSupportFiniteRestriction l E T n) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits T
    (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finite quotient restriction is right exact. Source: Stacks Tag 03DA
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable instance sfCompactSupportFiniteRestrictionColimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (sfCompactSupportFiniteRestriction l E T n) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits T
    (Padic.coefficientExtensionTransition l E (n + 1))

/-- The completion projections commute with the specified finite quotient transition.
Source: Stacks Tag 03CO; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-compact-support-constructible).
Proof: the completed sheaf is the inverse limit of the finite quotient tower.
Its cone condition identifies the higher projection followed by the quotient map
with the lower projection. Forgetting commutativity gives exactly this condition
for ring sheaves; faithfulness lifts it back to commutative ring sheaves. -/
theorem sfCompactSupportProjection_transition (T : Scheme.{u}) (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E T (n + 1) ≫
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift) =
      completedIntegralCommRingProjectionUnrestricted l E T n := by
  sorry

/-- The sectionwise identity composite restriction comparison, supplied by the shared
commutative ring-sheaf restriction interface. Source: Stacks Tags 03DA and 03CO
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportRestrictionComp (T : Scheme.{u}) (n : ℕ) :
    sfCompactSupportFiniteRestriction l E T n ⋙
        scalarReductionRestriction.{u, u} l E T (n + 1) ≅
      scalarReductionRestriction.{u, u} l E T n :=
  pbcRestrictComp (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift))
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (sfCompactSupportProjection_transition l E T n)

/-- Exact restriction composition on derived categories. Source: Stacks Tag 015F
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportDerivedRestrictionComp (T : Scheme.{u}) (n : ℕ) :
    (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory ⋙
        scalarReductionDerivedRestriction.{u, u} l E T (n + 1) ≅
      scalarReductionDerivedRestriction.{u, u} l E T n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfCompactSupportRestrictionComp l E T n)

/-- The canonical reduction map at the finite coefficient level. It is the adjunct
of the lower reduction unit under the higher reduction/restriction adjunction.
On a K-flat representative it is precisely x tensor a ↦ x tensor rho(a), since that
adjunction's unit is x ↦ x tensor 1 and the restriction comparison is identity on
sections. Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tags 03EK and 07A6
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportReductionTransition (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E T (n + 1)).obj K ⟶
      (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory.obj
        ((scalarReductionDerivedExtension.{u, u} l E T n).obj K) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E T (n + 1)).choose.homEquiv
    K _).symm
    ((sfDerivedReductionUnit l E T n).app K ≫
      (sfCompactSupportDerivedRestrictionComp l E T n).inv.app
        ((scalarReductionDerivedExtension.{u, u} l E T n).obj K))


variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The actual term Res_n R(c.g)_* c.i_! (K tensor^L A_n), where the natural index
n denotes exponent n+1. Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportTerm
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E Y) :=
  (scalarReductionDerivedRestriction.{u, u} l E Y n).obj
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))

/-- The specified quotient transition: apply compact support at the higher level to
the reduction map, apply the compact-support restriction comparison, and restrict to
completed coefficients. The final identity-on-sections comparison identifies the two
composite restrictions. Source: Bhatt--Scholze, Sections 6.5 and 6.7
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    sfCompactSupportTerm l E c K (n + 1) ⟶ sfCompactSupportTerm l E c K n :=
  (scalarReductionDerivedRestriction.{u, u} l E Y (n + 1)).map
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (sfCompactSupportReductionTransition l E X K n) ≫
      (sfCompactSupportRestriction c
        (Padic.coefficientExtensionTransition l E (n + 1))).hom.app
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
    (sfCompactSupportDerivedRestrictionComp l E Y n).hom.app
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))

/-- Every derived limit of the specified finite-level compact-support tower is bounded
constructible and derived complete, with one cohomological interval for all reductions.
Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0GL0
(blueprint: lem-sf-integral-compact-support-constructible).

Proof plan:
1. The compactification's middle scheme is finite type over the base field, hence
Noetherian; its open part is quasi-compact. Choose the closed complement. The completed
and finite coefficient restrictions are compatible with every quotient projection.
2. The ringed open--closed exact sequence and preservation of products by immersion
restriction show that completed-coefficient extension by zero preserves countable
products and hence Roos triangles. Its exactness makes its derived functor triangulated.
3. Resolve K by a K-flat complex. The slice extension/tensor identity shows its extension
by zero remains K-flat, and identifies every finite reduction with c.i_! K_n. Naturality
of the tensor identity identifies both the quotient maps and the reduction units.
4. Apply extension by zero to K's completion Roos triangle. The preceding product,
transition and unit identifications prove that the extended object is derived complete.
5. Extend each finite stratification by the closed complement, with zero module there.
Exact extension by zero preserves cohomology, constructibility and the common interval.
6. Apply lem-sf-integral-direct-image-constructible to c.g and this integral constructible
extension. It supplies constructible reductions with one uniform enlarged interval.
7. The reduction comparisons and lem-sf-compact-support-restriction-of-scalars identify
its ordinary proper-image tower with the terms and transitions defined above. Derived
limit morphisms and levelwise isomorphisms identify any chosen limit with this one.
8. Reduction functoriality and naturality of units transport derived completeness and
the common constructible interval through that isomorphism. No canonical comparison
between arbitrary chosen derived limits is asserted. -/
theorem sfIntegralCompactSupport_constructible
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K)
    [HasProduct (sfCompactSupportTerm l E c K)]
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (_hM : IsDerivedLimit (sfCompactSupportTransition l E c K) M) :
    sfIntegralConstructible l E Y M := by
  sorry

end WeilConjectures
