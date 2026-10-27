module

public import Sheaf.Geometry.Manifold.HermitianDolbeaultData

/-!
# Coordinate differential expressions on complex forms

Source: Kong, Notes on Complex Geometry, §6.2, definition preceding Lemma 6.4
(blueprint: def-sfb-form-differential-expressions).

Coefficients act on alternating tensors in the real coordinate frame. Ordered lists of
coordinate directions encode partial derivatives; summing equal multi-indices gives the
usual multi-index expression. Only the lists of length exactly `k` enter the degree-`k`
symbol. No symbol or differential operator is supplied independently of its coefficients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open scoped Manifold ContDiff

namespace ComplexManifold

/-- The constant coordinate space of complex-valued real alternating `a`-tensors.
Source: Kong §3.1 (blueprint: def-sfb-form-differential-expressions). -/
abbrev FormTensor (n a : ℕ) := ContinuousAlternatingMap ℝ (Model n) ℂ (Fin a)

/-- The fibre of type `(p,q)`, described by the complex-structure eigenspace condition.
It is zero outside the permitted type range. Source: Kong §3.1
(blueprint: def-sfb-form-differential-expressions). -/
def typeTensor (n : ℕ) (p q : ℤ) : Set (FormTensor n (p + q).toNat) :=
  {τ | if 0 ≤ p ∧ p ≤ n ∧ 0 ≤ q ∧ q ≤ n then
    ∀ v : Fin (p + q).toNat → Model n,
      (∑ j : Fin (p + q).toNat, τ (Function.update v j (Complex.I • v j))) =
        ((p - q : ℤ) : ℂ) * Complex.I * τ v
    else τ = 0}

/-- A local expression of order at most `k`, with smooth coefficient homomorphisms
between ambient alternating tensor spaces. Its restriction to a type fibre will be used
for a type operator. Source: Kong §6.2, definition preceding Lemma 6.4
(blueprint: def-sfb-form-differential-expressions). -/
structure FormDifferentialExpression (n a b k : ℕ) (U : Set (Model n)) where
  coefficient : (l : Fin (k + 1)) → (Fin l.val → Fin n × Bool) →
    Model n → FormTensor n a →L[ℂ] FormTensor n b
  smooth : ∀ (l : Fin (k + 1)) (j : Fin l.val → Fin n × Bool),
    ContDiffOn ℝ ∞ (coefficient l j) U

/-- Apply the actual finite coordinate differential expression to a tensor field.
The empty directional list is the term of order zero. Source: Kong §6.2
(blueprint: def-sfb-form-differential-expressions). -/
def FormDifferentialExpression.apply {n a b k : ℕ} {U : Set (Model n)}
    (A : FormDifferentialExpression n a b k U) (f : Model n → FormTensor n a)
    (z : Model n) : FormTensor n b :=
  ∑ l : Fin (k + 1), ∑ j : Fin l.val → Fin n × Bool,
    A.coefficient l j z (iteratedFDerivWithin ℝ l.val f U z
      (fun t ↦ realCoordinateVector (j t)))

/-- The homogeneous degree-`k` principal symbol, evaluated at a real covector.
The convention is `∂_j ↦ ξ_j`, with no factor of `i`. Source: Kong §6.2
(blueprint: def-sfb-form-differential-expressions). -/
def FormDifferentialExpression.symbol {n a b k : ℕ} {U : Set (Model n)}
    (A : FormDifferentialExpression n a b k U) (z : Model n)
    (ξ : Model n →L[ℝ] ℝ) : FormTensor n a →L[ℂ] FormTensor n b :=
  ∑ j : Fin k → Fin n × Bool,
    ((∏ t : Fin k, ξ (realCoordinateVector (j t))) : ℂ) •
      A.coefficient ⟨k, Nat.lt_succ_self k⟩ j z

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]

/-- The coordinate expression represents the restriction of `L` from type `(p,q)` to
`(r,s)` in chart `e`. Coefficients are compared on every smooth input section of the
source type. Source: Kong §6.2 (blueprint: def-sfb-form-differential-expressions). -/
def FormDifferentialExpression.Represents {k : ℕ} {p q r s : ℤ}
    (e : OpenPartialHomeomorph M (Model n))
    (A : FormDifferentialExpression n (p + q).toNat (r + s).toNat k e.target)
    (L : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)) : Prop :=
  ∀ α : typeForms (n := n) (M := M) p q, ∀ z ∈ e.target,
    formCoordinates (L α.val).val (r + s).toNat e z =
      A.apply (formCoordinates α.val.val (p + q).toNat e) z

/-- Smooth differential order at most `k` between two type spaces: the map has the
specified bidegree and is locally a finite sum of smooth coefficients times partial
derivatives of order at most `k`. Source: Kong §6.2
(blueprint: def-sfb-form-differential-expressions). -/
def HasFormDifferentialOrder (k : ℕ) (p q r s : ℤ)
    (L : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)) : Prop :=
  (∀ α : typeForms (n := n) (M := M) p q, L α.val ∈ typeForms r s) ∧
  ∀ e : OpenPartialHomeomorph M (Model n), e ∈ atlas (Model n) M →
    ∃ A : FormDifferentialExpression n (p + q).toNat (r + s).toNat k e.target,
      A.Represents e L

/-- Ellipticity of a type endomorphism: in each chart its degree-`k` symbol, formed from
its actual top-order coefficients, is a bijection on every type fibre at each nonzero
real covector. The second bijection explicitly regards the same symbol as real-linear.
Source: Kong §6.2, definition preceding Lemma 6.4 and realification
(blueprint: def-sfb-form-differential-expressions). -/
def IsFormElliptic (k : ℕ) (p q : ℤ)
    (L : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)) : Prop :=
  (∀ α : typeForms (n := n) (M := M) p q, L α.val ∈ typeForms p q) ∧
  ∀ e : OpenPartialHomeomorph M (Model n), e ∈ atlas (Model n) M →
    ∃ A : FormDifferentialExpression n (p + q).toNat (p + q).toNat k e.target,
      A.Represents e L ∧ ∀ z ∈ e.target, ∀ ξ : Model n →L[ℝ] ℝ, ξ ≠ 0 →
        Set.BijOn (A.symbol z ξ) (typeTensor n p q) (typeTensor n p q) ∧
        Set.BijOn ((A.symbol z ξ).restrictScalars ℝ)
          (typeTensor n p q) (typeTensor n p q)

end ComplexManifold
