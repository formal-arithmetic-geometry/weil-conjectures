module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.GroupTheory.MonoidLocalization.Away
import WeilConjectures.LinearAlgebra.NonzeroMaximalMinorOfInjective
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Generic affine-linear perturbations have full-rank Jacobian

Source: Stacks Project, examples-defos.tex, Tag 0E7U, lemma-jouanolou-type-thing,
its statement and rank-deficient incidence proof
(blueprint: lem-sfb-generic-linear-perturbation-jacobian).

The constructions below are the displayed specialized equations, their quotient,
and the images of their maximal Jacobian minors. The theorem gives a single nonzero
parameter polynomial valid after every field extension, including the empty-equation case.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace MvPolynomial.GenericLinearPerturbation

variable {k : Type u} [Field k] {L : Type v} [Field L] {N c : ℕ}

/-- The specialized equation `f_j + b_{0j} + ∑ b_{ij} x_i` after coefficient extension
along `φ`. Row `0` supplies constants and row `i.succ` the coefficient of `X i`.
Source: Stacks Project, Tag 0E7U, displayed equations
(blueprint: lem-sfb-generic-linear-perturbation-jacobian). -/
def equation (φ : k →+* L) (f : Fin c → MvPolynomial (Fin N) k)
    (b : Fin (N + 1) → Fin c → L) (j : Fin c) : MvPolynomial (Fin N) L :=
  MvPolynomial.map φ (f j) + MvPolynomial.C (b 0 j) +
    ∑ i : Fin N, MvPolynomial.C (b i.succ j) * MvPolynomial.X i

/-- The specified algebra `L[x₁,…,x_N]/(h₁,…,h_c)`, with its canonical `L`-algebra
structure. No nontriviality condition is imposed.
Source: Stacks Project, Tag 0E7U, fibres of the displayed family
(blueprint: lem-sfb-generic-linear-perturbation-jacobian). -/
abbrev Quotient (φ : k →+* L) (f : Fin c → MvPolynomial (Fin N) k)
    (b : Fin (N + 1) → Fin c → L) :=
  MvPolynomial (Fin N) L ⧸ Ideal.span (Set.range (equation φ f b))

/-- The image in the specified quotient of a `c × c` Jacobian minor, with columns
selected by an embedding. All orderings of the selected columns are allowed; their
signs do not change the generated ideal. For `c = 0` there is one embedding, and
`Matrix.det` of its empty matrix is `1`.
Source: Stacks Project, Tag 0E7U, Jacobian rank condition
(blueprint: lem-sfb-generic-linear-perturbation-jacobian). -/
def minor (φ : k →+* L) (f : Fin c → MvPolynomial (Fin N) k)
    (b : Fin (N + 1) → Fin c → L) (r : Fin c ↪ Fin N) : Quotient φ f b :=
  Ideal.Quotient.mk _
    (Matrix.det (fun j l : Fin c ↦ MvPolynomial.pderiv (r l) (equation φ f b j)))

/-- A single nonzero polynomial in the affine-linear perturbation parameters cuts out
an open on which all maximal Jacobian minors generate the unit ideal and the specified
quotient is smooth over the coefficient field. When `c = 0`, this polynomial can be `1`.
Source: Stacks Project, examples-defos.tex, Tag 0E7U, lemma-jouanolou-type-thing,
statement and rank-deficient incidence proof, extended to `c = 0` by the empty determinant
(blueprint: lem-sfb-generic-linear-perturbation-jacobian).

Proof plan, following the node's six steps:
1. If `c = 0`, take `H = 1`. The unique empty determinant is `1`; the polynomial
   algebra is standard smooth with no equations. Standard smooth implies smooth,
   and the affine comparison gives smoothness of the spectrum map.
2. Otherwise put `P = k[z]`, `K = Frac(P)`, and form `D = P[x]/(g_j, Δ_I)` using
   the universal equations and their maximal minors. If `D_K` is nonzero, choose
   a maximal ideal and its residue field `E`, using
   `lem-weil-pbc-proper-ideal-contained-in-maximal` and localization at a prime.
   The unital field map `K → E` is injective, so the `M = c(N+1)` parameter images
   are algebraically independent over `k` (def-kun-transcendence-degree).
3. All maximal minors of the Jacobian vanish in `E`. Contrapositively apply
   `lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor` to its transpose.
   Transposition preserves determinants by the Leibniz formula. A nonzero kernel
   vector, renumbered and normalized, has first entry `1`. Its equations express
   every `a_{i1}` through the `x_i`, the remaining coefficients, and `c-1` lambdas.
   The derivative in this identity is `∂_i f_1`, correcting the source's index typo.
4. The equations `g_j = 0` also express all constant coefficients `a_{0j}`.
   Hence all `M` parameters lie in the subfield generated by `N+(c-1)+N(c-1)=M-1`
   elements. This field is the fraction field of the algebra they generate:
   fractions form the smallest subfield containing these generators. Each fraction
   satisfies `bT-a`, so `lem-sfb-algebraic-adjoin-transcendence-bound` bounds its
   transcendence degree by `M-1`. Algebraic independence of the `M` parameters
   contradicts this. Thus `D_K = 0`.
5. Equality `1/1 = 0` in this localization yields a nonzero `H ∈ P` killed in `D`,
   by the equality criterion of def-weil-pbc-module-localization. Express its ideal
   membership as `H = ∑ A_j g_j + ∑ C_I Δ_I`. Substitute any `φ : k → L` and any
   parameter tuple where `H` is nonzero, then pass to the quotient using
   def-weil-pbc-algebra-hom-quotient. Partial derivatives and determinants commute
   with coefficient substitution by their monomial and Leibniz formulas. Inverting
   the nonzero scalar `H(b)` shows the images of the minors span the unit ideal.
   This identity remains valid for the zero quotient algebra.
6. On each principal chart of a minor `δ`, adjoining `y` with `yδ = 1` gives the
   localization presentation with Jacobian block determinant `δ²`: select the
   minor's columns followed by `y` and expand along the last column. The inverse
   maps send `y` to `δ⁻¹` and `v/δ^r` to `vy^r`. Since `c+1 ≤ N+1`, this is a
   standard smooth presentation, also when the localization is zero. Apply
   lem-weil-pbc-standard-smooth-is-smooth, then
   lem-weil-pbc-smooth-ring-map-local-on-cover to the minors' unit-ideal cover.
   Finally lem-weil-pbc-smooth-ring-map-iff-smooth-affine gives the spectrum claim.
-/
theorem exists_nonzero_parameter_polynomial (k : Type u) [Field k]
    (N c : ℕ) (hc : c ≤ N) (f : Fin c → MvPolynomial (Fin N) k) :
    ∃ H : MvPolynomial (Fin (N + 1) × Fin c) k,
      H ≠ 0 ∧ (c = 0 → H = 1) ∧
      ∀ (L : Type (max u v)) [Field L] (φ : k →+* L)
        (b : Fin (N + 1) → Fin c → L),
        MvPolynomial.eval₂ φ (fun ij ↦ b ij.1 ij.2) H ≠ 0 →
          Ideal.span (Set.range (minor φ f b)) = ⊤ ∧
          Smooth (Spec.map (CommRingCat.ofHom (algebraMap L (Quotient φ f b)))) := by
  sorry

end MvPolynomial.GenericLinearPerturbation
