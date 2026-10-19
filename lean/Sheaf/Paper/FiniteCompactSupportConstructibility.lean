/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars

import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.GroupTheory.Torsion
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness
import Sheaf.CategoryTheory.BoundedHeartAmplitude
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompactSupportDirectImageTriangulated
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Finite-level bounded constructibility for proper support

Source: Stacks Project, Tags 0GL0, 095U and 0GL6; current blueprint,
sec-six-functors-basics/sk-prop-sf-cbc/prop-finite-compact-support-constructibility
(blueprint: prop-finite-compact-support-constructibility).

We use intrinsic finite-torsion constructibility and the recorded compactification
candidate. The scalar comparison is the adjunct of compact support of the tensor unit,
followed by the recorded, normalized restriction-of-scalars comparison. In particular
it is the canonical B-linear map, not an unspecified isomorphism of underlying objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The recorded intrinsic compact-support candidate specialized to the actual finite
quotient, supplying its proved finiteness rather than asking for extra data.
Source: blueprint, compactification formula preceding the proposition; Stacks Tag 0GL0
(blueprint: prop-finite-compact-support-constructibility). -/
abbrev finiteLevelCompactSupport (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  @sfIntrinsicCompactSupport X Y f c (Padic.coefficientExtensionRing l E n) _
    (Padic.finite_coefficientExtensionRing l E n hn)

/-- The canonical composite shift structure: exact extension by zero followed by the
K-injective right derived direct image. Source: blueprint exactness clause; Stacks Tag 0GL0
(blueprint: prop-finite-compact-support-constructibility). -/
instance finiteLevelCompactSupport_commShift (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (finiteLevelCompactSupport l E n hn c).CommShift ℤ :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  inferInstanceAs (((sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E n)).mapDerivedCategory ⋙
      proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E n)).CommShift ℤ)

/-- The actual quotient map, sheafified on the original small pro-etale site.
Source: blueprint, finite reduction clause; Stacks Tag 0GL6
(blueprint: prop-finite-compact-support-constructibility). -/
abbrev finiteLevelReductionMap (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u}) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
      (S := Padic.coefficientExtensionIdeal l E n)
      (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))))

/-- Ordinary unbounded derived extension along A_{E,n} to A_{E,m}.
This specializes the published K-flat derived-change-of-rings construction, retaining
its canonical universal counit and tensor-unit-normalized scalar adjunction.
Source: Stacks Tags 06YY and 0GL6 (blueprint: prop-finite-compact-support-constructibility). -/
abbrev finiteLevelDerivedReduction (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u}) :=
  pbcDerivedExtend (finiteLevelReductionMap l E m n hmn T)

/-- The canonical coefficient comparison is the scalar-adjunction transpose of
compact support of the tensor unit followed by the specified restriction comparison.
The latter is normalized on sections, on open adjunction units and on K-injectives.
Source: Stacks Tag 0GL6 and the blueprint proof, Steps 6--7
(blueprint: prop-finite-compact-support-constructibility). -/
def finiteLevelCompactSupportReductionComparison
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) :
    (finiteLevelDerivedReduction l E m n hmn Y).obj
        ((finiteLevelCompactSupport l E n (hm.trans hmn) c).obj K) ⟶
      (finiteLevelCompactSupport l E m hm c).obj
        ((finiteLevelDerivedReduction l E m n hmn X).obj K) :=
  letI := Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)
  letI := Padic.finite_coefficientExtensionRing l E m hm
  ((pbcDerivedScalarAdjunction (finiteLevelReductionMap l E m n hmn Y)).homEquiv _ _).symm
    ((finiteLevelCompactSupport l E n (hm.trans hmn) c).map
        ((pbcDerivedScalarAdjunction (finiteLevelReductionMap l E m n hmn X)).unit.app K) ≫
      (sfCompactSupportRestriction c (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m)
        (Ideal.pow_le_pow_right hmn))).hom.app
          ((finiteLevelDerivedReduction l E m n hmn X).obj K))

/-- Finite-level compact support restricts to an exact triangulated functor on the
intrinsic bounded constructible subcategories. The interval is chosen before both the
compactification and the input. Reduction is asserted only when its actual derived
scalar extension is bounded constructible; there is no finite-Tor-amplitude assumption.
Both endpoints of the canonical comparison belong to Dbc. Its reduced output has the
specified interval [c,d+2e], uniformly in the positive reduction level and compactification.
The coherent candidate and its identity/cocycle comparisons are those of the recorded
compactification-coherence theorem, restricted to these etale-origin objects.

Source: blueprint prop-finite-compact-support-constructibility, statement and proof,
Steps 1--7; Stacks Tags 0GL0, 095U and 0GL6
(blueprint: prop-finite-compact-support-constructibility).

Proof:
1. The finite quotient is killed by a power of l, which is invertible on the schemes.
   Every compactification is finite type over the field and hence Noetherian.
2. Descend the bounded intrinsically constructible input to the etale site. Exact,
   fully faithful comparison pullback commutes with cohomology and reflects its zero
   objects, so it preserves and reflects the input interval.
3. Exact etale extension by zero preserves constructible cohomology. Proper direct
   image preserves bounded constructibility. The proper/open site comparison carries
   this result back to the intrinsic pro-etale candidate.
4. The finite-type compact-support vanishing theorem, applied to the original f,
   gives [0,2e] for a constructible sheaf. Apply successive truncation triangles and
   their cohomology long exact sequences to obtain [a,b+2e] for a complex in [a,b].
   This does not transfer the fibre bound to the boundary of a compactification.
5. The ambient candidate is triangulated. Preservation from Step 3 restricts this
   exact functor to the full bounded constructible subcategories with induced triangles.
   The recorded canonical refinement comparisons give the identity and cocycle laws.
6. For ordinary derived scalar extension, proper torsion projection formula and the
   open tensor comparison give the coefficient isomorphism on the etale site. Their
   tensor-unit/counit normalizations identify it with the displayed scalar-adjunction
   transpose. Restriction of scalars detects isomorphisms. No perfectness of B is used.
7. Exact site comparison and its K-flat scalar comparison identify the reduced input.
   Full faithfulness reflects constructibility and vanishing, so its assumed bounded
   constructibility permits the comparisons at both coefficient levels. Transport
   Step 6 back. Step 3 gives bounded constructibility of the target, and the isomorphism
   gives it for the source. Step 4 at B yields [c,d+2e], uniformly in m and the candidate.
   If c > d, the reduced input is zero, and its image satisfies every interval bound. -/
theorem finiteCompactSupportConstructibility
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ c : Compactification f,
      (finiteLevelCompactSupport l E n hn c).IsTriangulated ∧
      ∀ K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n),
        intrinsicFiniteTorsionConstructible l E n hn X K →
        intrinsicFiniteTorsionConstructible l E n hn Y
          ((finiteLevelCompactSupport l E n hn c).obj K)) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ (e : ℕ),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) →
      ∃ a' b' : ℤ, a' ≤ b' ∧ ∀ (c : Compactification f)
        (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
        intrinsicFiniteTorsionConstructible l E n hn X K →
        DerivedCategory.homologyConcentratedIn a b K →
        intrinsicFiniteTorsionConstructible l E n hn Y
            ((finiteLevelCompactSupport l E n hn c).obj K) ∧
          DerivedCategory.homologyConcentratedIn a' b'
            ((finiteLevelCompactSupport l E n hn c).obj K)) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (c : Compactification f)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
      intrinsicFiniteTorsionConstructible l E n hn X K →
      intrinsicFiniteTorsionConstructible l E m hm X
        ((finiteLevelDerivedReduction l E m n hmn X).obj K) →
      IsIso (finiteLevelCompactSupportReductionComparison l E m n hm hmn c K) ∧
      intrinsicFiniteTorsionConstructible l E m hm Y
        ((finiteLevelDerivedReduction l E m n hmn Y).obj
          ((finiteLevelCompactSupport l E n hn c).obj K)) ∧
      intrinsicFiniteTorsionConstructible l E m hm Y
        ((finiteLevelCompactSupport l E m hm c).obj
          ((finiteLevelDerivedReduction l E m n hmn X).obj K)) ∧
      ∀ (e : ℕ),
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
          topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) →
        ∀ (a b : ℤ),
          DerivedCategory.homologyConcentratedIn a b
            ((finiteLevelDerivedReduction l E m n hmn X).obj K) →
          DerivedCategory.homologyConcentratedIn a (b + 2 * (e : ℤ))
            ((finiteLevelCompactSupport l E m hm c).obj
              ((finiteLevelDerivedReduction l E m n hmn X).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
