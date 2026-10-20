/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.DerivedComplete
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.SequentialTowerEvaluationFull
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.PbcRoosTriangle
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Effectivity of normalized DVR towers

Source: Weil conjectures blueprint, sec-six-functors, sk-prop-sf-biduality-general,
order 2132 (blueprint: lem-coef-normalized-dvr-effectivity).

The derived limit is specified by its Roos triangle on actual derived evaluations.
Comparisons are adjoints of the specified limit projections. Coherence is an equality
in the finite-coefficient derived category, including both identity and longer quotient
maps. No constructibility, boundedness, or Tor-amplitude hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The actual completed-coefficient tensor-restriction adjunction, normalized on
K-flat representatives by the tensor unit x ↦ x tensor 1.
Source: Stacks Tags 06YY and 0DVC; blueprint order 2132
(blueprint: lem-coef-normalized-dvr-effectivity). -/
def normalizedDVRIntegralAdjunction (n : ℕ) :
    scalarReductionDerivedExtension l E X n ⊣ scalarReductionDerivedRestriction l E X n :=
  (derivedScalarExtensionRestrictionAdjunction l E X n).choose

/-- The canonical reduction transition is adjoint to the smaller quotient unit,
transported through the canonical composition comparison for restrictions.
Source: blueprint order 2132, last proof paragraph
(blueprint: lem-coef-normalized-dvr-effectivity). -/
def normalizedDVRReductionTransition (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m)
    (M : completedIntegralDerivedCategory l E X D hl) :
    (scalarReductionDerivedExtension l E X m).obj M ⟶
      (normalizedDVRRes l E X h).obj
        ((scalarReductionDerivedExtension l E X n).obj M) :=
  ((normalizedDVRIntegralAdjunction l E X m).homEquiv M _).symm
    ((normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
      (normalizedDVRResCompletedComp l E X D hl h).inv.app
        ((scalarReductionDerivedExtension l E X n).obj M))

/-- The counit comparison at a finite level is the adjoint of that limit projection.
Source: blueprint order 2132, comparison in the statement
(blueprint: lem-coef-normalized-dvr-effectivity). -/
def normalizedDVRCounitComparison (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj M ⟶ T.M n :=
  ((normalizedDVRIntegralAdjunction l E X n).homEquiv M (T.M n)).symm
    (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom)

/-- A normalized DVR tower is recovered by derived reduction of its derived inverse
limit, through coherent canonical counit isomorphisms; that inverse limit is derived
complete. Source: blueprint order 2132; Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-coef-normalized-dvr-effectivity).

Proof plan:
1. The valuation ring is a DVR (lem-weil-l-adic-extension-integers-dvr). Flatness of
its completed constant sheaf and its finite quotients
(lem-weil-pbc-constant-completion-equivalence) show that [R →^{ϖ^n} R], in degrees
[-1,0], is a two-term finite free resolution of B_n. It is K-flat since tensoring it
with an acyclic complex gives an acyclic multiplication cone (def-pc-kflat-complex,
def-pc-tensor-complex-sheaves, lem-sf-derived-homology-long-exact).
2. Successively choose roofs for the finite transitions and K-flat resolutions with
flat terms (lem-pc-quasi-isomorphisms-multiplicative-system, lem-pc-kflat-resolution).
This gives strict semilinear chain maps. Longer maps are composites; the given
cocycle identifies them with every specified transition. After restriction to R,
lem-weil-pbc-sequential-tower-evaluation-full lifts the level identifications to an
isomorphism of coherent derived towers, preserving all projections.
3. Fix n and discard the finite initial segment, using the Roos triangle
(prop-weil-pbc-roos-triangle). For m ≥ n the augmentation
[B_m →^{ϖ^n} B_m] → B_n has fiber B_n[1], identified by multiplication by ϖ^(m-n).
Reduction from m' to m acts on this fiber by ϖ^(m'-m).
4. Tensor these strict coefficient triangles with the K-flat representatives Q_m.
Tensor reassociation gives a triangle of strict towers with middle terms
Q_m tensor_R [R →^{ϖ^n} R], right terms Q_m tensor_{B_m} B_n, and left terms the
latter shifted by one with transitions multiplied by ϖ^(m'-m).
Normalization identifies the right tower with the constant Q_n tower, compatibly
with every transition (def-coef-normalized-dvr-tower, lem-pur-derived-change-of-rings).
5. Every n successive left transitions are zero. Its product shift s satisfies
s^n=0, so 1-s has inverse 1+s+...+s^(n-1). Its Roos limit is zero; exact derived
inverse limit therefore identifies the middle and right limits
(lem-weil-pbc-ringed-strict-tower-homotopy-limit). The constant-tower limit is Q_n:
the difference map on products is split surjective by finite partial sums and has
kernel the diagonal Q_n.
6. Exact countable products on the pro-etale site and
lem-weil-derived-limit-products-core compute these products termwise. Tensoring
with the two-term finite free resolution commutes with products, shifts and the
Roos cone, even for unbounded Q_m. Hence the middle limit is M tensor_R^L B_n.
The map to Q_n is the adjoint of the original limit projection, by the ordinary
tensor formulas and derived adjunction (lem-pc-derived-adjoint-functors).
Restriction detects acyclic cones because it changes no underlying abelian sheaf
(def-pc-sheaf-restrict-scalars), so this is an isomorphism in D(B_n).
7. Composing a limit projection with any transition gives the smaller projection.
Taking adjoints proves exactly the displayed coherence equation. Transporting the
original Roos triangle through these comparisons makes the canonical reduction
augmentation of M the first map of a Roos triangle, which is IsDerivedComplete.
No constructibility or boundedness enters any step. -/
theorem normalizedDVRTower_effectivity (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) :
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
          normalizedDVRReductionTransition l E X D hl h M ≫
            (normalizedDVRRes l E X h).map
              (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
      IsDerivedComplete l E X D hl M := by
  sorry

end WeilConjectures
