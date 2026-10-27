module

public import Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials
public import Sheaf.AlgebraicGeometry.RationalNormalCurve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.RingTheory.Length
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Component projection bounds for leading Hilbert weights

Source: Morrison, arXiv:0810.2340, §3.2, Theorem 8 proof steps (2)--(3), p.14;
Gieseker, Lectures on Moduli of Curves, Proposition 1.0.3, pp.30--36.
(blueprint: lem-sfb-component-projection-weight-bounds)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.BoundedHilbertWeight

/-- The canonical polynomial restriction family, characterized on every standard chart
using the existing degree-zero cohomology-to-sections identification. This is precisely
the normalization of the arrows in exists_uniform_bounded_hilbert_weights.
Source: Morrison §2.2; §3.2 Theorem 8 steps (2)--(3).
(blueprint: lem-sfb-component-projection-weight-bounds) -/
def IsPolynomialRestriction {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    (i : X ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k)))
    (ρ : ∀ m : ℕ, ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
        sections k n i m) : Prop :=
  ∀ (m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m)
    (j : HilbertPlucker.Coordinates.{u} n),
    ((Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))).presheaf.map
        (homOfLE le_top).op ((UniformProjectiveFibreVanishing.zeroSections _).hom (ρ m p)) =
      Scheme.Modules.tensorPullbackSection i
        (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))
        (ProjectiveSpace.standardOpen _ (Spec (.of k)) j)
        (ProjectiveSpace.chartRingEquiv _ k j (MvPolynomial.dehomogenizeX k j p.val) •
          ProjectiveSpace.twistGenerator _ (Spec (.of k)) (m : ℤ) j)

/-- The two component-projection estimates, with no Hilbert-semistability hypothesis.
Here r = n + 2. Degree is the Euler degree of the pulled-back hyperplane line on the
canonical normalization. The quotient dimension is the existing coordinateDimension:
its defining equations are exactly W = ker(V → H⁰(Y,O(1))). The zero-stage flag equality
and the bound w ≤ 1 specify weight zero on W and weight one on V/W.

Source: Morrison §3.2, Theorem 8 steps (2)--(3); Gieseker Proposition 1.0.3, pp.30--36.
(blueprint: lem-sfb-component-projection-weight-bounds)

Proof (the five DAG steps):
1. The positive linear Hilbert polynomial gives dimension one. Finite type over a field
   gives Noetherianity and finitely many components. Connectedness excludes isolated
   zero-dimensional components. Integral-curve span-degree rigidity gives s ≤ e+1 and
   s ≤ e in the non-rational-normal case. Primary-complement separation supplies the
   generic multiplicity μ, the complementary scheme C of degree δ=d-μe, and an exponent Q
   for injective restriction of I_Y^t to C when t≥Q.
2. If μ≥2 then d≥2e; the numerical assumptions give s<r (separate e=1 and e≥2).
   In the second case s≤e≤3<r. Nondegeneracy of X_red forces Y to be proper. Connectedness
   supplies a point P of Y∩C on a curve component of C, hence δ>0. Generic reducedness
   makes μ=1 in the second case.
3. For a compatible basis let β_j be the dimension of the span of degree-m monomials
   of weight at most j. These have m-j factors vanishing on Y and thus on P. For
   m-j≥Q, injective restriction to C and the point-power section bound give
   β_j≤δm-(m-j)+K, uniformly in j. Bound the remaining Q-1 terms by P(m).
4. Greedily extending monomial bases along the weight filtration attains the minimum.
   Summation by parts gives w_F(m)=mP(m)-Σ_{j<m}β_j. Summing the preceding estimates
   yields w_F(m)≥(μe+1/2)m²-O(m). Divide by m² and use the prescribed asymptotic
   coefficient from bounded Hilbert weights to obtain a_F≥μe+1/2.
5. For μ≥2 this is a_F≥2e+1/2; for μ=1 it is a_F≥e+1/2. Combine with step 1's
   respective span bounds. No step uses semistability. -/
theorem component_projection_weight_bounds
    (k : Type u) [Field k] [IsAlgClosed k] (n d : ℕ) (c : ℤ)
    (hr : 4 ≤ n + 2) (hd : 3 < d) (hdr : (d : ℚ) / (n + 2 : ℕ) < 8 / 7)
    (X : Scheme.{u}) (i : X ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k)))
    [IsClosedImmersion i] [ConnectedSpace X]
    (hP : ProjectiveHilbertPolynomial.IsCoordinatePolynomial k (n + 1) i
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)))
    (hnd : ProjectiveHilbertPolynomial.equations k (n + 1)
      (X.nilradical.subschemeι ≫ i) 1 = ⊥)
    (Y : Scheme.{u}) [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j]
    (hY : Set.range j ∈ irreducibleComponents X) (e : ℕ)
    (he : @Scheme.Modules.degree k _ Y.normalization
      ⟨Y.fromNormalization ≫ j ≫ i ≫
        (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k))⟩
      ((Scheme.Modules.tensorPullback (Y.fromNormalization ≫ j ≫ i)).obj
        (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1)) = (e : ℤ))
    (ρ : ∀ m : ℕ, ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
        sections k n i m) (hρ : IsPolynomialRestriction i ρ)
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) (hw : ∀ l, w l ≤ 1)
    (hF : flag b w 0 = ProjectiveHilbertPolynomial.equations k (n + 1) (j ≫ i) 1)
    (a : ℚ) (ha : ∃ A M : ℕ, ∀ m : ℕ, M ≤ m →
      |(weight (ρ m) b w : ℚ) - a * (m : ℚ)^2| ≤ (A : ℚ) * m) :
    (2 ≤ Module.length (X.presheaf.stalk (j (genericPoint Y)))
        (X.presheaf.stalk (j (genericPoint Y))) →
      ProjectiveHilbertPolynomial.coordinateDimension k (n + 1) (j ≫ i) 1 ≤ e + 1 ∧
        (2 * (e : ℚ) + 1 / 2 ≤ a)) ∧
    ((∀ x : X, closure {x} ∈ irreducibleComponents X →
        _root_.IsReduced (X.presheaf.stalk x)) →
      e ≤ 3 → ¬ IsRationalNormalCurve k (n + 1) (j ≫ i) e →
      ProjectiveHilbertPolynomial.coordinateDimension k (n + 1) (j ≫ i) 1 ≤ e ∧
        ((e : ℚ) + 1 / 2 ≤ a)) := by
  sorry

end AlgebraicGeometry.BoundedHilbertWeight
