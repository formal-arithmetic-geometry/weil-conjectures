module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Smooth differential operators and their coordinate symbols

Source: Demailly, Complex Analytic and Differential Geometry, VI §1, (1.1)–(1.3)
(blueprint: def-sfb-smooth-differential-operator).

Multi-indices are bounded componentwise by the requested order. The sum is further
restricted by total degree, so this includes exactly the usual multi-indices. Derivatives
are iterated coordinate derivatives, with no factor of `i`. Local presentations use the
given smooth bundle trivializations and coordinate charts, on smaller open neighborhoods.
The symbol is read from any such presentation, avoiding a choice of coefficients.
-/

@[expose] public section

noncomputable section

universe u v w v₁ w₁

open Bundle
open scoped ContDiff Manifold

namespace SmoothDifferentialOperator

/-- The mixed partial `∂^α`, with real coordinate derivatives.
Source: Demailly VI §1, (1.1) (blueprint: def-sfb-smooth-differential-operator). -/
def mixedPartial {m : ℕ} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : Fin m → ℕ) (f : (Fin m → ℝ) → F) : (Fin m → ℝ) → F :=
  (List.finRange m).foldr
    (fun j g ↦ (fun h y ↦ fderiv ℝ h y (Pi.single j 1))^[α j] g) f

/-- The coordinate expression `∑ b_α ∂^α` through degree `d`.
Source: Demailly VI §1, (1.1) (blueprint: def-sfb-smooth-differential-operator). -/
def coordinateExpression {m d : ℕ} {F : Type v} {K : Type w}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
    (b : (Fin m → Fin (d + 1)) → (Fin m → ℝ) → F →L[ℝ] K)
    (f : (Fin m → ℝ) → F) (y : Fin m → ℝ) : K :=
  ∑ α ∈ Finset.univ.filter (fun α : Fin m → Fin (d + 1) ↦ ∑ j, (α j).val ≤ d),
    b α y (mixedPartial (fun j ↦ (α j).val) f y)

/-- The degree-`d` symbol of a coordinate presentation, evaluated on a covector `ξ`.
Source: Demailly VI §1, (1.2)–(1.3)
(blueprint: def-sfb-smooth-differential-operator). -/
def coordinateSymbol {m d : ℕ} {F : Type v} {K : Type w}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
    (b : (Fin m → Fin (d + 1)) → (Fin m → ℝ) → F →L[ℝ] K)
    (y ξ : Fin m → ℝ) : F →L[ℝ] K :=
  ∑ α ∈ Finset.univ.filter (fun α : Fin m → Fin (d + 1) ↦ ∑ j, (α j).val = d),
    (∏ j, ξ j ^ (α j).val) • b α y

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin m → ℝ) M]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type w} [NormedAddCommGroup K] [NormedSpace ℝ K]
  {G : M → Type v₁} {H : M → Type w₁}
  [TopologicalSpace (TotalSpace F G)] [TopologicalSpace (TotalSpace K H)]
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℝ (G x)]
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℝ (H x)]
  [FiberBundle F G] [VectorBundle ℝ F G] [FiberBundle K H] [VectorBundle ℝ K H]

/-- The coordinate representative of a section in the chart and bundle frame centered at `p`.
Source: Demailly VI §1, (1.1) (blueprint: def-sfb-smooth-differential-operator). -/
def sectionCoordinates (p : M) (s : ∀ x, G x) (y : Fin m → ℝ) : F :=
  (trivializationAt F G p).continuousLinearMapAt ℝ ((chartAt (Fin m → ℝ) p).symm y)
    (s ((chartAt (Fin m → ℝ) p).symm y))

/-- A smooth local coefficient presentation for a linear operator on global smooth sections.
The open domain lies in both frame domains and the chart target. Coefficients of degree
greater than `d` are ignored. Source: Demailly VI §1, (1.1)
(blueprint: def-sfb-smooth-differential-operator). -/
def IsLocalPresentation {d : ℕ}
    (Q : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G →ₗ[ℝ]
      ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H)
    (p : M) (U : Set (Fin m → ℝ))
    (b : (Fin m → Fin (d + 1)) → (Fin m → ℝ) → F →L[ℝ] K) : Prop :=
  IsOpen U ∧ (chartAt (Fin m → ℝ) p) p ∈ U ∧
    U ⊆ (chartAt (Fin m → ℝ) p).target ∧
    Set.MapsTo (chartAt (Fin m → ℝ) p).symm U
      ((trivializationAt F G p).baseSet ∩ (trivializationAt K H p).baseSet) ∧
    (∀ α, (∑ j, (α j).val) ≤ d → ContDiffOn ℝ ∞ (b α) U) ∧
    ∀ (s : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G) (y : Fin m → ℝ), y ∈ U →
      sectionCoordinates p (Q s) y = coordinateExpression b (sectionCoordinates p s) y

/-- A real-linear differential operator with smooth coefficients and order at most `d`.
Source: Demailly VI §1, (1.1) (blueprint: def-sfb-smooth-differential-operator). -/
def IsSmoothDifferentialOperator (d : ℕ)
    (Q : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G →ₗ[ℝ]
      ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H) : Prop :=
  ∀ p : M, ∃ U b, IsLocalPresentation (d := d) Q p U b

/-- The fibre map given by the degree-`d` coordinate symbol, transported from the model
fibres into the actual fibres. The covector is expressed in the chart centered at `p`.
Source: Demailly VI §1, (1.2) (blueprint: def-sfb-smooth-differential-operator). -/
def presentationSymbol {d : ℕ} (p : M)
    (b : (Fin m → Fin (d + 1)) → (Fin m → ℝ) → F →L[ℝ] K)
    (ξ : Fin m → ℝ) : G p →L[ℝ] H p :=
  ((trivializationAt K H p).symmL ℝ p).comp
    ((coordinateSymbol b ((chartAt (Fin m → ℝ) p) p) ξ).comp
      ((trivializationAt F G p).continuousLinearMapAt ℝ p))

end SmoothDifferentialOperator
