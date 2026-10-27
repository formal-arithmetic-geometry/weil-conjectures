module

public import Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.AlgebraicGeometry.DivisorModule

/-! # Subcurve spans and selected boundary branches

Source: Morrison, arXiv:0810.2340, Section 3.2, proof steps (7), (9)--(10);
Gieseker, Proposition 1.0.7, pp.55--61, selected-boundary version.
(blueprint: lem-sfb-subcurve-span-weight-bound)

The reduction and its component union may be presented by any reduced closed
immersions with the specified images. Polynomial restriction arrows are fixed on
standard charts, and the leading coefficient is specified by its quadratic error.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.SubcurveSpanWeight

/-- The pulled-back hyperplane line, on the actual embedded scheme.
Source: Morrison §3.2 (blueprint: lem-sfb-subcurve-span-weight-bound). -/
def hyperplane {k : Type u} [Field k] {n : ℕ} {T : Scheme.{u}}
    (j : T ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))) : T.Modules :=
  (Scheme.Modules.tensorPullback j).obj
    (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1)

/-- The degree on the canonical normalization of a reduced integral component.
Source: Morrison §3.2, degree convention of the selected-boundary estimate
(blueprint: lem-sfb-subcurve-span-weight-bound). -/
def componentDegree {k : Type u} [Field k] {n : ℕ} {C : Scheme.{u}} [IsIntegral C]
    (j : C ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))) : ℤ :=
  @Scheme.Modules.degree k _ C.normalization
    ⟨C.fromNormalization ≫ j ≫
      (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k))⟩
    (hyperplane (C.fromNormalization ≫ j))

/-- The chart characterization of polynomial restriction. This fixes the arrow uniquely;
no freely chosen evaluation map replaces the embedded scheme's sections.
Source: Morrison §2.2 and §3.2; the chart convention of
lem-sfb-bounded-hilbert-weight-polynomials
(blueprint: lem-sfb-subcurve-span-weight-bound). -/
def IsRestriction {k : Type u} [Field k] {n : ℕ} {T : Scheme.{u}}
    (j : T ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))) (m : ℕ)
    (ρ : ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
        BoundedHilbertWeight.sections k n j m) : Prop :=
  ∀ (p : MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m)
    (a : HilbertPlucker.Coordinates.{u} n),
    ((Scheme.Modules.tensorPullback j).obj
      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n)
        (Spec (.of k)) (m : ℤ))).presheaf.map (homOfLE le_top).op
          ((UniformProjectiveFibreVanishing.zeroSections _).hom (ρ p)) =
      Scheme.Modules.tensorPullbackSection j
        (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))
        (ProjectiveSpace.standardOpen _ (Spec (.of k)) a)
        (ProjectiveSpace.chartRingEquiv _ k a (MvPolynomial.dehomogenizeX k a p.val) •
          ProjectiveSpace.twistGenerator _ (Spec (.of k)) (m : ℤ) a)

/-- The geometric zero/one weight estimate for any selected distinct boundary branches.
No semistability assumption is made. Components and the reduced support are enumerated
without repetition, and S may be disconnected.

Source: Morrison §3.2, proof steps (7), (9)--(10); Gieseker Proposition 1.0.7,
pp.55--61, selected-boundary version, with the rational-normal exception in the DAG.
(blueprint: lem-sfb-subcurve-span-weight-bound)

Proof (the six DAG steps):
1. Restriction has kernel W, so V/W injects into H⁰(Y,L); rank-nullity gives s ≤ h⁰.
   The bounded Hilbert-weight-polynomials lemma supplies eventual monomial bases and
   w_F(m)=a_F m²+O(m), for any adapted basis of the zero/one flag.
2. Projective-curve-normalization-section-defect gives bounded kernel for restriction
   to the normalized components, component dimensions me_E+O(1), and total dimension
   m sum e_E+O(1), uniformly in the weight cutoff j. Separate complementary components
   into I with b_E≤e_E and J satisfying the rational-normal exception.
3. Nodal-subcurve-boundary makes each selected point a smooth complementary branch.
   A form in W vanishes there. A monomial of weight at most j<m has at least m-j W
   factors, vanishes on Y, and vanishes to order m-j at each selected branch.
4. Smooth-curve-section-degree-cap bounds its image on E in I by
   me_E-b_E(m-j)+1. On J, W restricts to sections of degree e_E-b_E=-1 and is zero.
   Rank-nullity and step 2 give h_m-dim U_(m,j) at least
   me_Y+sum_(J) me_E+sum_(I) b_E(m-j)-C. Embedded nilpotents affect only C.
5. For any monomial basis, count a monomial of weight t once for each j<t.
   Summing the preceding codimensions gives weight at least
   m²(e_Y+sum_(J)e_E+sum_(I)b_E/2)-Cm, hence the same for its minimum.
6. Divide by m² and use the quadratic error to obtain the coefficient inequality.
   On J, e_E=b_E-1≥b_E/2 because b_E≥2. This gives a_F≥e_Y+b/2.
   Zero selected branches and disconnected Y require no modification. -/
theorem subcurve_span_weight_bound
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (X D Y : Scheme.{u}) [ConnectedSpace X]
    (i : X ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k)))
    [IsClosedImmersion i] (hdim : topologicalKrullDim X = 1)
    (hgeneric : ∀ x : X, closure ({x} : Set X) ∈ irreducibleComponents X →
      _root_.IsReduced (X.presheaf.stalk x))
    (δ : D ⟶ X) [IsClosedImmersion δ] [IsReduced D]
    (hred : Function.Surjective δ)
    (hnondegenerate : ProjectiveHilbertPolynomial.equations k (n + 1) (δ ≫ i) 1 = ⊥)
    (hnodal : ∀ x : D, x ∈ closedPoints D →
      ¬((δ ≫ i ≫ (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘
        Spec (.of k))).stalkMap x).hom.FormallySmooth →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk x))
        (D.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (t : ℕ) (C : Fin t → Scheme.{u}) [∀ a, IsIntegral (C a)]
    (j : ∀ a, C a ⟶ D) (hclosed : ∀ a, IsClosedImmersion (j a))
    (hdistinct : Function.Injective (fun a ↦ Set.range (j a)))
    (hcomponents : ∀ E : Set D,
      E ∈ irreducibleComponents D ↔ ∃ a, Set.range (j a) = E)
    (S : Finset (Fin t)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (y : Y ⟶ D) [IsClosedImmersion y] [IsReduced Y]
    (hY : Set.range y = ⋃ a ∈ S, Set.range (j a))
    (selected : ∀ a, Finset (C a).normalization)
    (hselected : ∀ a, a ∉ S → ∀ p ∈ selected a,
      p ∈ closedPoints (C a).normalization ∧
        j a ((C a).fromNormalization p) ∈ Set.range y)
    (hdegree : ∀ a, a ∉ S → 0 < componentDegree (j a ≫ δ ≫ i))
    (hexception : ∀ a, a ∉ S →
      ((selected a).card : ℤ) ≤ componentDegree (j a ≫ δ ≫ i) ∨
      (componentDegree (j a ≫ δ ≫ i) = ((selected a).card : ℤ) - 1 ∧
        2 ≤ (selected a).card ∧
        ∃ e : C a ≅ ℙ(HilbertPlucker.Coordinates.{u} 0; Spec (.of k)),
          e.hom ≫ (ℙ(HilbertPlucker.Coordinates 0; Spec (.of k)) ↘ Spec (.of k)) =
            j a ≫ δ ≫ i ≫
              (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k)) ∧
          ∃ σ : ModuleCat.of k (BoundedHilbertWeight.LinearForms k n) ⟶
              BoundedHilbertWeight.sections k n (j a ≫ δ ≫ i) 1,
            IsRestriction (j a ≫ δ ≫ i) 1 σ ∧ Function.Surjective σ))
    (ρ : ∀ m : ℕ, ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
        BoundedHilbertWeight.sections k n i m)
    (hρ : ∀ m, IsRestriction i m (ρ m))
    (basis : Module.Basis (HilbertPlucker.Coordinates.{u} n) k
      (BoundedHilbertWeight.LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) (hw : ∀ a, w a ≤ 1)
    (hflag : BoundedHilbertWeight.flag basis w 0 =
      ProjectiveHilbertPolynomial.equations k (n + 1) (y ≫ δ ≫ i) 1)
    (aF : ℚ)
    (haF : ∃ m₀ A : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∃ M, BoundedHilbertWeight.IsMonomialBasis (ρ m) basis M) ∧
      |(BoundedHilbertWeight.weight (ρ m) basis w : ℚ) - aF * (m : ℚ)^2| ≤
        (A : ℚ) * m) :
    Module.finrank k ((BoundedHilbertWeight.LinearForms k n) ⧸
      ProjectiveHilbertPolynomial.equations k (n + 1) (y ≫ δ ≫ i) 1) ≤
        Module.finrank k (BoundedHilbertWeight.sections k n (y ≫ δ ≫ i) 1) ∧
      (∑ a ∈ S, (componentDegree (j a ≫ δ ≫ i) : ℚ)) +
        (∑ a ∈ Sᶜ, ((selected a).card : ℚ)) / 2 ≤ aF := by
  sorry

end AlgebraicGeometry.SubcurveSpanWeight
