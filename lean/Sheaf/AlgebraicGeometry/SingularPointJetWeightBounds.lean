/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveCurveJetWeightData
public import Sheaf.AlgebraicGeometry.DivisorModule
import Sheaf.AlgebraicGeometry.NormalizationJetCodimension
import Sheaf.AlgebraicGeometry.CoherentFiniteSupportSkyscrapers
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Singular-point jet flags give lower bounds for Hilbert weights

Source: Morrison, arXiv:0810.2340, §3.2, Theorem 8(4)--(6), pp.14--15;
Gieseker, Proposition 1.0.6, pp.49--55, for the two tangent-line cases.
(blueprint: lem-sfb-singular-point-jet-weight-bounds)

The coefficient is a_F=e_F/2. Component labels on branches retain self-intersections.
The reduction and both polynomial restriction families are canonical constructions,
with the latter characterized chart by chart rather than arbitrary linear maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.BoundedHilbertWeight AlgebraicGeometry.ProjectiveCurveBranches

namespace AlgebraicGeometry.ProjectiveCurveJets

/-- The multiplicity, ramified-branch, and tangent-double-point bounds, together with
invariance of every leading coefficient under the finite-length nilradical.
The number of coordinates is n+2; no one-dimensional embedded curve is excluded.
Singular closed points are expressed by nonregular local rings over the perfect field.

Source: Morrison §3.2 Theorem 8(4)--(6), pp.14--15; Gieseker Proposition 1.0.6.
(blueprint: lem-sfb-singular-point-jet-weight-bounds)

Proof, following the seven DAG steps:
1. Finite type over a Noetherian field gives finitely many irreducible components.
   Connectedness and dimension one exclude isolated zero-dimensional components, so the
   reduction is pure one-dimensional. Sort restricted degree-m monomials by weight,
   retaining each new independent vector. The minimum total basis weight is the sum,
   for 0≤j<Bm, of the codimensions of the weight-at-most-j spans. Use the bounded
   Hilbert weight-polynomial theorem for eventual spanning and quadratic coefficients.
2. For the point flag, evaluation has rank one. Weight-at-most-j monomials vanish to
   order b_q(m-j) on every branch. The branch multiplicity theorem gives sum b_q=t and
   the component degree bounds. The normalization jet-codimension theorem gives
   codimension at least t(m-j)-C. Summing gives t*m*(m+1)/2-C*m and hence a_F≥t/2.
3. A degree-at-most-three rational normal component has nonzero normalization tangent
   map on both standard charts of P¹. Thus a ramified component has degree at least four.
   Orders 2,3,4 impose at most one new coefficient each; evaluation has rank one.
   The jet flag therefore has total weight at most 4+2+1=7 and order+weight≥4.
4. Monomials of weight at most j<4m have branch order at least 4m-j. Apply jet
   codimension using degree≥4 and sum the orders to obtain 8m²+O(m), hence a_F≥8.
5. At a nonnodal double point with unramified normalization, the branch theorem gives
   two branches with a common tangent. Its equations have codimension two and the
   point equations codimension one. The 0,1,2 flag has total weight three. If neither
   branch is a line, component degrees accommodate order 2m-j at both points. This
   includes two points on one component: its degree is at least four by rational
   normality in low degrees. Summing codimensions gives 4m²+O(m), hence a_F≥4.
6. If one branch lies on a line, the other is on a distinct component of degree≥2.
   For j<m, monomials vanish identically on the line: impose order m there and
   2m-j on the other branch. For m≤j<2m impose order 2m-j on both. The sums of
   3m-j-C and 4m-2j-C over these intervals give (7/2)m²+O(m).
7. Generic reducedness makes the nilradical have finite support and length ℓ.
   The coherent finite-support skyscraper theorem bounds the restriction kernel by ℓ,
   also after twisting. For large m restriction is surjective. A minimum monomial
   basis on the reduction lifts by the same monomials and extends using at most ℓ
   more, each of weight at most Bm. Conversely select a basis after restriction from
   a minimum basis on X. Thus 0≤w_X(m)-w_D(m)≤Bℓm and the coefficients agree.
   This transfers all three estimates to X without Hilbert semistability. -/
theorem singular_point_jet_weight_bounds
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (X : Scheme.{u}) [ConnectedSpace X]
    (i : X ⟶ Ambient k (n + 2)) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X = 1)
    (hgeneric : ∀ x : genericPoints X, _root_.IsReduced (X.presheaf.stalk x.val))
    (hspan : ∀ f : LinearForms k n,
      (∀ p : Reduction X, VanishesAt ((reductionMap X ≫ i) p) f) → f = 0)
    (hlow : ∀ Z : irreducibleComponents (Reduction X),
      componentDegree k (n + 2) (Reduction X) (reductionMap X ≫ i) Z ≤ 3 →
        IsRationalNormal
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨Z.val, isClosed_of_mem_irreducibleComponents _ Z.property⟩).subschemeι ≫
              reductionMap X ≫ i)) :
    ∃ (ρX : ∀ m : ℕ, ModuleCat.of k
          (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
          sections k n i m)
      (ρD : ∀ m : ℕ, ModuleCat.of k
          (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
          sections k n (reductionMap X ≫ i) m),
      IsRestriction i ρX ∧ IsRestriction (reductionMap X ≫ i) ρD ∧
      (∀ (p : Reduction X) (t : ℕ), HasMultiplicity (Reduction X) p t → 3 ≤ t →
        ∃ (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
          (w : HilbertPlucker.Coordinates.{u} n → ℕ) (a : ℚ),
          IsPointFlag ((reductionMap X ≫ i) p) b w ∧ (∑ j, w j) = 1 ∧
            HasCoefficient ρX b w a ∧ (t : ℚ) / 2 ≤ a) ∧
      (∀ (p : Reduction X) (q : Branch (Reduction X) p),
        tangentImage k (n + 2) (Reduction X) (reductionMap X ≫ i) p q = {0} →
        4 ≤ componentDegree k (n + 2) (Reduction X) (reductionMap X ≫ i) q.1 ∧
        ∃ (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
          (w : HilbertPlucker.Coordinates.{u} n → ℕ) (a : ℚ),
          IsRamifiedFlag (reductionMap X ≫ i) p q b w ∧ (∑ j, w j) ≤ 7 ∧
            HasCoefficient ρX b w a ∧ 8 ≤ a) ∧
      ((∀ (p : Reduction X),
          ∀ q : Branch (Reduction X) p,
            tangentImage k (n + 2) (Reduction X) (reductionMap X ≫ i) p q ≠ {0}) →
        (∀ (p : Reduction X),
          ¬ IsRegularLocalRing ((Reduction X).presheaf.stalk p) →
            HasMultiplicity (Reduction X) p 2) →
        ∀ (p : Reduction X),
          HasMultiplicity (Reduction X) p 2 →
          ¬ HasSplitNodeCompletion k (n + 2) (Reduction X) (reductionMap X ≫ i) p →
          ∃ (q : Branch (Reduction X) p)
            (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
            (w : HilbertPlucker.Coordinates.{u} n → ℕ) (a : ℚ),
            (∀ q' : Branch (Reduction X) p,
              lineEquations k (n + 2) (Reduction X) (reductionMap X ≫ i) p q' =
                lineEquations k (n + 2) (Reduction X) (reductionMap X ≫ i) p q) ∧
            IsTangentFlag (reductionMap X ≫ i) p q b w ∧ (∑ j, w j) ≤ 3 ∧
            HasCoefficient ρX b w a ∧ 7 / 2 ≤ a ∧
            ((∀ q' : Branch (Reduction X) p,
              componentDegree k (n + 2) (Reduction X) (reductionMap X ≫ i) q'.1 ≠ 1) →
              4 ≤ a)) ∧
      (∀ (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
        (w : HilbertPlucker.Coordinates.{u} n → ℕ) (a : ℚ),
        HasCoefficient ρX b w a ↔ HasCoefficient ρD b w a) := by
  sorry

end AlgebraicGeometry.ProjectiveCurveJets
