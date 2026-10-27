module

public import Sheaf.Analysis.EuclideanWeakSobolev
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Sobolev localization across two bundle charts

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, atlas independence;
Differential and pseudodifferential operators on manifolds, §2, pp.3–4, (2.2), (2.2 prime),
and Lemma 2.3. The integer weak chain-rule argument is made explicit in the DAG.
(blueprint: lem-sfb-sobolev-chart-overlap-bound)
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace BundleSobolev

open Classical in
/-- The ordinary product/chain-rule coefficients for a matrix multiplier and a coordinate
map. A word differentiates from its head to its tail. At each step differentiate the old
coefficient and add the terms differentiating the composed function. The predecessor
multi-index is used only when its indicated component is positive.
Source: Demailly §2, pp.3–4, atlas independence, explicit recursion in the DAG proof step 4
(blueprint: lem-sfb-sobolev-chart-overlap-bound). -/
def overlapChainCoefficient {m r : ℕ} (A : Model m → Matrix (Fin r) (Fin r) ℝ)
    (F : Model m → Model m) :
    List (Fin m) → (Fin m → ℕ) → Model m → Matrix (Fin r) (Fin r) ℝ
  | [], β, y => if β = 0 then A y else 0
  | i :: w, β, y =>
      fun k l ↦
        fderiv ℝ (fun z ↦ overlapChainCoefficient A F w β z k l) y
          (EuclideanSpace.single i 1) +
        ∑ j : Fin m, if 0 < β j then
          (fderiv ℝ (fun z ↦ F z j) y (EuclideanSpace.single i 1)) *
            overlapChainCoefficient A F w (fun a ↦ β a - if a = j then 1 else 0) y k l
        else 0

open Classical in
/-- The weak Leibniz/chain expression for a multi-index, extended by zero off the overlap.
The finite sum includes exactly the input derivatives of order at most the output order.
Source: Demailly §2, pp.3–4, atlas independence; DAG proof steps 4 and 6
(blueprint: lem-sfb-sobolev-chart-overlap-bound). -/
def overlapWeakDerivative {m r : ℕ} (D : Set (Model m))
    (A : Model m → Matrix (Fin r) (Fin r) ℝ) (F : Model m → Model m)
    (α : Fin m → ℕ) (f : Model m → Model r) (k : Fin r) (y : Model m) : ℝ :=
  if y ∈ D then
    ∑ β : Fin m → Fin ((∑ i, α i) + 1),
      if (∑ i, (β i : ℕ)) ≤ ∑ i, α i then
        ∑ l : Fin r,
          overlapChainCoefficient A F
            (List.ofFn (fun i : Fin m ↦ List.replicate (α i) i)).flatten
            (fun i ↦ (β i : ℕ)) y k l *
          weakDerivative (fun i ↦ (β i : ℕ)) (fun x ↦ f x l) (F y)
      else 0
  else 0

variable {m r : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Model m) M]
  (E : M → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Model r) E)]
  [FiberBundle (Model r) E] [VectorBundle ℝ (Model r) E]

/-- The matrix of multiplication by the cutoff followed by the U-to-V frame change,
expressed in V coordinates. Only its restriction to the overlap is used.
Source: Demailly §2, pp.3–4, (2.2), atlas independence; DAG proof step 2
(blueprint: lem-sfb-sobolev-chart-overlap-bound). -/
def overlapMultiplier (cV : OpenPartialHomeomorph M (Model m))
    (eU eV : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) E → M))
    [eU.IsLinear ℝ] [eV.IsLinear ℝ] (η : M → ℝ) (y : Model m) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun k l ↦ η (cV.symm y) *
    (eU.coordChangeL ℝ eV (cV.symm y) (EuclideanSpace.single l 1)) k

open Classical in
/-- The components of η times the section with U components f and zero elsewhere,
transported to V coordinates and extended by zero. The overlap test makes the zero
extension outside U explicit, including when the two charts are disjoint.
Source: Demailly §2, pp.3–4, atlas independence; DAG proof step 2
(blueprint: lem-sfb-sobolev-chart-overlap-bound). -/
def overlapTransform (cU cV : OpenPartialHomeomorph M (Model m))
    (eU eV : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) E → M))
    [eU.IsLinear ℝ] [eV.IsLinear ℝ] (η : M → ℝ) (f : Model m → Model r)
    (y : Model m) : Model r :=
  if y ∈ (cV.symm ≫ₕ cU).source then
    WithLp.toLp 2 (fun k ↦ ∑ l : Fin r,
      overlapMultiplier E cV eU eV η y k l * f (cU (cV.symm y)) l)
  else 0

/-- Multiplication and transition between two smooth bundle charts is bounded for the exact
integer weak Sobolev norm, on functions supported a.e. in a fixed compact set. The next
clause gives every derivative by the explicit product/chain recursion, and the last integral
is precisely the dual transformation with the absolute inverse Jacobian on tests. The a.e.
clause ensures this is a map on L² classes, independent of all representatives.
Source: Demailly VI §2, atlas independence; Differential and pseudodifferential operators
on manifolds, §2, pp.3–4, (2.2), (2.2 prime), Lemma 2.3
(blueprint: lem-sfb-sobolev-chart-overlap-bound).

Proof plan:
1. If r=0, K is empty, or η=0 the operator is zero and C=1 works. Otherwise cover
cU(K) by finitely many smaller concentric balls compactly contained in cU.target.
Use lem-sfb-euclidean-smooth-ball-bump and lem-sfb-real-smooth-differentiation to form
χ=1-∏(1-βj), compactly supported inside cU.target and equal to one near cU(K).
2. On D=(cV.symm ≫ₕ cU).source put F=cU∘cV.symm and B equal to the frame matrix.
A=η∘cV.symm · χ∘F · B has compact support L inside D, and extends smoothly by zero.
For inputs supported on cU(K), Rf=A(f∘F) agrees a.e. with overlapTransform.
3. Apply lem-sfb-euclidean-jacobian-nonnegative-integrability to F inverse on F(L).
The supremum of each matrix coefficient and of the absolute inverse Jacobian gives
‖a(h∘F)‖₂² ≤ M_a² J ‖h‖₂². The integrability clause supplies measurability, and the
indicator version shows inverse images of null sets are null, giving a.e. independence.
4. Induct on differentiation words using lem-sfb-real-smooth-differentiation. The recursion
is overlapChainCoefficient. All coefficients have support in L. Finite Cauchy–Schwarz
and step 3 bound the sum of derivative squared norms by N² M² J times the input sum.
5. For smooth compactly supported inputs, lem-sfb-continuous-compact-support-integrable
makes the products integrable; repeated lem-sfb-scalar-integrable-integration-by-parts
identifies classical and distributional derivatives, with sign (-1)^|α|.
6. Apply lem-sfb-euclidean-sobolev-graph-mollification inside cU.target to approximate f
by smooth compactly supported functions in the weak Sobolev norm. Step 3 makes every
recursion term converge in L². Its closed-graph clause identifies the limiting weak
derivatives and passes the finite estimate to the limit. Remove χ since it is one near
cU(K) and all weak derivatives vanish locally outside this set. Take C=N M sqrt J > 0.
7. Pair against each vector test and apply lem-sfb-euclidean-jacobian-integral to F inverse.
The resulting dual test has the transposed frame matrix and absolute inverse Jacobian.
Insert χ to give compact support inside cU.target; it acts identically on f. This proves
the stated test identity, including orientation-reversing transitions. The same identity
with differentiated tests gives the already identified distributional derivatives.
-/
theorem sobolev_chart_overlap_bound
    [T2Space M] [IsManifold 𝓘(ℝ, Model m) ∞ M]
    [ContMDiffVectorBundle ∞ (Model r) E 𝓘(ℝ, Model m)]
    (hm : 1 ≤ m) (cU cV : OpenPartialHomeomorph M (Model m))
    (hcU : cU ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ M)
    (hcV : cV ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model m) ∞ M)
    (eU eV : Trivialization (Model r) (TotalSpace.proj : TotalSpace (Model r) E → M))
    [eU.IsLinear ℝ] [eV.IsLinear ℝ]
    (heU : eU ∈ trivializationAtlas (Model r) E)
    (heV : eV ∈ trivializationAtlas (Model r) E)
    (hU : cU.source ⊆ eU.baseSet) (hV : cV.source ⊆ eV.baseSet)
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ cU.source)
    (η : M → ℝ) (hη : ContMDiff 𝓘(ℝ, Model m) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) (hηV : tsupport η ⊆ cV.source) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Model m → Model r,
      EuclideanMem s f → (∀ᵐ x ∂volume, x ∉ cU '' K → f x = 0) →
      EuclideanMem s (overlapTransform E cU cV eU eV η f) ∧
      euclideanNorm s (overlapTransform E cU cV eU eV η f) ≤ C * euclideanNorm s f ∧
      (∀ α : Fin m → ℕ, (∑ i, α i) ≤ s → ∀ k : Fin r,
        IsWeakDerivative ⊤ α (fun y ↦ overlapTransform E cU cV eU eV η f y k)
          (overlapWeakDerivative (cV.symm ≫ₕ cU).source
            (overlapMultiplier E cV eU eV η) (fun y ↦ cU (cV.symm y)) α f k)) ∧
      (∀ g : Model m → Model r, f =ᵐ[volume] g →
        overlapTransform E cU cV eU eV η f =ᵐ[volume]
          overlapTransform E cU cV eU eV η g) ∧
      (∀ ψ : Model m → Model r, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ y, ∑ k : Fin r, overlapTransform E cU cV eU eV η f y k * ψ y k) =
          ∫ x in (cU.symm ≫ₕ cV).source,
            |LinearMap.det (fderiv ℝ (fun z ↦ cV (cU.symm z)) x).toLinearMap| *
              ∑ k : Fin r, ∑ l : Fin r,
                f x l * overlapMultiplier E cV eU eV η (cV (cU.symm x)) k l *
                  ψ (cV (cU.symm x)) k) := by
  sorry

end BundleSobolev
