module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend

import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Rational polynomial additive-bar contraction

Source: main-20261015, six-functors basics, direct-images proof, paragraph (3),
algebraic obligation below the trivial-lattice calculation
(blueprint: lem-sfb-rational-polynomial-bar-contraction).

The node supplies an agent-formulated algebraic lemma, rather than a quoted
assertion in the blueprint. Its prescribed ordered representatives and signed
projection are implemented below. Natural-number degrees present the nonnegative
complex; `polynomialComplex` and `exteriorComplex` extend it by zero to integers.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open scoped BigOperators

namespace RationalPolynomialBar

/-- Degree `n` polynomials in `n` blocks of `r` coordinates (indices start at zero).
Source: the displayed definition of P in the algebraic obligation below
main-20261015 direct-images paragraph (3)
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
abbrev P (B : Type u) [CommRing B] (r n : ℕ) :=
  MvPolynomial (Fin n × Fin r) B

/-- The basis of degree `q` exterior representatives consists of subsets of size `q`.
Source: the displayed definition of K in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
abbrev ExteriorIndex (r q : ℕ) := {I : Finset (Fin r) // I.card = q}

/-- The free module on the indicated subsets; it is zero when `q > r`.
Source: the definition of K in the algebraic obligation below
main-20261015 direct-images paragraph (3)
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
abbrev K (B : Type u) [CommRing B] (r q : ℕ) := ExteriorIndex r q →₀ B

/-- The inner coface merges blocks `a` and `a+1` by addition.
Source: the displayed bar differential in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def merge (B : Type u) [CommRing B] (r n : ℕ) (a : Fin n) :
    P B r n →ₐ[B] P B r (n + 1) :=
  MvPolynomial.aeval fun (b, i) ↦
    if b < a then MvPolynomial.X (b.castSucc, i)
    else if b = a then MvPolynomial.X (b.castSucc, i) + MvPolynomial.X (b.succ, i)
    else MvPolynomial.X (b.succ, i)

/-- The full unnormalized additive-bar differential, including both outer cofaces.
Source: the displayed differential for P in the algebraic obligation below
main-20261015 direct-images paragraph (3)
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def differential (B : Type u) [CommRing B] (r n : ℕ) :
    P B r n →ₗ[B] P B r (n + 1) :=
  (MvPolynomial.aeval (fun (b, i) ↦ MvPolynomial.X (b.succ, i))).toLinearMap +
    ∑ a : Fin n, (-1 : B) ^ (a.val + 1) • (merge B r n a).toLinearMap +
    (-1 : B) ^ (n + 1) •
      (MvPolynomial.aeval (fun (b, i) ↦ MvPolynomial.X (b.castSucc, i))).toLinearMap

/-- Send the subset basis vector to its ordered coordinate product; the empty
product is 1. Source: the prescribed i in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def inclusion (B : Type u) [CommRing B] (r q : ℕ) : K B r q →ₗ[B] P B r q :=
  Finsupp.linearCombination B fun I ↦
    ∏ a : Fin q, MvPolynomial.X (a, I.val.orderEmbOfFin I.property a)

/-- The exponent vector of a monomial having one specified coordinate per block.
Source: the prescribed p in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def coordinateExponent (r q : ℕ) (j : Fin q → Fin r) : (Fin q × Fin r) →₀ ℕ :=
  ∑ a : Fin q, Finsupp.single (a, j a) 1

/-- The sign of sorting a tuple, computed as a product of -1 over inversions.
Source: the sorting sign in the prescribed p in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def sortingSign (B : Type u) [CommRing B] (r q : ℕ) (j : Fin q → Fin r) : B :=
  ∏ a : Fin q, ∏ b : Fin q, if a < b ∧ j b < j a then -1 else 1

/-- The subset indexed by an injective tuple of coordinates.
Source: the prescribed p in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def coordinateSubset (r q : ℕ) (j : Fin q → Fin r) (hj : Function.Injective j) :
    ExteriorIndex r q :=
  ⟨Finset.univ.image j, (Finset.card_image_of_injective Finset.univ hj).trans
    (Fintype.card_fin q)⟩

/-- Projection of one monomial: only injective, one-coordinate-per-block tuples
contribute. For degree zero the unique empty tuple selects the constant monomial.
Source: the prescribed p in the algebraic obligation below
main-20261015 direct-images paragraph (3)
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def projectMonomial (B : Type u) [CommRing B] (r q : ℕ)
    (m : (Fin q × Fin r) →₀ ℕ) : K B r q :=
  ∑ j : Fin q → Fin r,
    if hj : Function.Injective j then
      if m = coordinateExponent r q j then
        Finsupp.single (coordinateSubset r q j hj) (sortingSign B r q j)
      else 0
    else 0

/-- Extend the prescribed monomial projection B-linearly. In degree zero this is
1_B under the canonical identifications of P⁰ and K⁰ with B.
Source: the prescribed p in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def projection (B : Type u) [CommRing B] (r q : ℕ) : P B r q →ₗ[B] K B r q :=
  (MvPolynomial.basisMonomials (Fin q × Fin r) B).constr B (projectMonomial B r q)

/-- Extend a rational linear map by its monomial matrix. Each column is a genuine
polynomial, hence a finite rational linear combination of monomials.
Source: the scalar-extension clause of the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def extendHomotopy (B : Type u) [CommRing B] [Algebra ℚ B] (r n : ℕ)
    (h : P ℚ r (n + 1) →ₗ[ℚ] P ℚ r n) : P B r (n + 1) →ₗ[B] P B r n :=
  (MvPolynomial.basisMonomials (Fin (n + 1) × Fin r) B).constr B fun m ↦
    MvPolynomial.map (algebraMap ℚ B) (h (MvPolynomial.monomial m 1))

/-- The prescribed bar differential squares to zero.
Source: main-20261015 direct-images paragraph (3), algebraic obligation, proof step 1
(blueprint: lem-sfb-rational-polynomial-bar-contraction).

Proof: substitutions by adjacent addition and the two outer omissions satisfy
δᵇδᵃ = δᵃδᵇ⁻¹ for a < b, by associativity and the unit law. Expand the two
alternating sums. Every composite occurs twice with opposite signs, giving zero.
In degree zero the two constant substitutions cancel. Polynomial substitutions
are determined by their values on variables. -/
theorem differential_squared (B : Type u) [CommRing B] [Algebra ℚ B] (r n : ℕ) :
    (differential B r (n + 1)).comp (differential B r n) = 0 := by
  sorry

/-- The polynomial complex in nonnegative degrees, with its displayed differential.
Only the proof of d² = 0 is postponed, in the named theorem above.
Source: the definition of P in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def polynomialComplexNat (B : Type u) [CommRing B] [Algebra ℚ B] (r : ℕ) :
    CochainComplex (ModuleCat B) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of B (P B r n))
    (fun n ↦ ModuleCat.ofHom (differential B r n))
    (fun n ↦ congrArg ModuleCat.ofHom (differential_squared B r n))

/-- The exterior representative complex, with zero differential.
Source: the definition of K in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def exteriorComplexNat (B : Type u) [CommRing B] (r : ℕ) :
    CochainComplex (ModuleCat B) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of B (K B r q)) (fun _ ↦ 0) (by simp)

/-- P extended by zero in negative degrees using the standard embedding ℕ → ℤ.
Source: the negative-degree convention in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def polynomialComplex (B : Type u) [CommRing B] [Algebra ℚ B] (r : ℕ) :
    CochainComplex (ModuleCat B) ℤ :=
  (polynomialComplexNat B r).extend ComplexShape.embeddingUpNat

/-- K extended by zero in negative degrees; subsets of size q > r do not exist.
Source: the degree conventions in the same algebraic obligation
(blueprint: lem-sfb-rational-polynomial-bar-contraction). -/
def exteriorComplex (B : Type u) [CommRing B] (r : ℕ) :
    CochainComplex (ModuleCat B) ℤ :=
  (exteriorComplexNat B r).extend ComplexShape.embeddingUpNat

/-- The fixed ordered inclusion and signed projection give a deformation retraction,
with a single rational homotopy matrix extended to every coefficient algebra.
Source: main-20261015 direct-images paragraph (3), algebraic obligation, proof steps 2–8
(blueprint: lem-sfb-rational-polynomial-bar-contraction).

Proof: expand the coordinate products to get di = 0 by telescoping. For pd = 0,
outer omissions contribute nothing, while an inner coface contributes only a
quadratic merged block; its two orders have opposite sorting signs, and a repeated
coordinate vanishes. Directly pi = 1, including the empty subset.

Over ℚ split polynomials into total-coordinate multidegrees m. Divided monomials
form a finite basis in each degree. Dualizing gives a split simplicial module,
whose degenerate tuples are exactly those with zero blocks. Apply
`lem-sfb-split-simplicial-nondegenerate-homotopy`: its normalization homotopy identifies it with
the nonzero-block summand. The latter
has differential merging adjacent blocks with sign (-1)^a. Cumulative partial
sums identify it with augmented proper-product-interval chains shifted by two,
with the negative vertex-deletion differential. By
`lem-sfb-product-chain-proper-interval-homology`, homology vanishes unless
m is squarefree, in which case it is one-dimensional in degree |m|. Transpose
ranks identify the dual cohomology dimensions. For m = 0 only degree zero remains.
Since pi = 1, the prescribed i and p give inverse cohomology isomorphisms.

The kernel of p is therefore acyclic. By `lem-trf-vector-subspace-complement`,
choose rational complements Lⁿ to its cycles Zⁿ. Then d : Lⁿ → Zⁿ⁺¹ is bijective. On Zⁿ ⊕ Lⁿ take
the inverse of d on
the first summand and zero on the second; put h = 0 on i(K). This gives
dh + hd = 1 - ip. Sum over multidegrees. Every image of a monomial is a polynomial,
so its coefficient support is finite. The same rational matrices extend to B;
all identities are finite coefficient sums and persist without a nonzero-ring
assumption. For r = 0 the constant complex has dⁿ = 0 for even n, dⁿ = 1 for odd n,
and one may take hⁿ = 1 for even n ≥ 2, zero otherwise. -/
theorem contraction (r : ℕ) :
    ∃ h : ∀ n : ℕ, P ℚ r (n + 1) →ₗ[ℚ] P ℚ r n,
      ∀ (B : Type u) [CommRing B] [Algebra ℚ B],
        differential B r 0 = 0 ∧
        (∀ n : ℕ, (differential B r (n + 1)).comp (differential B r n) = 0) ∧
        (∀ q : ℕ, (differential B r q).comp (inclusion B r q) = 0) ∧
        (∀ q : ℕ, (projection B r (q + 1)).comp (differential B r q) = 0) ∧
        (∀ q : ℕ, (projection B r q).comp (inclusion B r q) = LinearMap.id) ∧
        (extendHomotopy B r 0 (h 0)).comp (differential B r 0) =
          LinearMap.id - (inclusion B r 0).comp (projection B r 0) ∧
        (∀ n : ℕ,
          (differential B r n).comp (extendHomotopy B r n (h n)) +
            (extendHomotopy B r (n + 1) (h (n + 1))).comp (differential B r (n + 1)) =
              LinearMap.id - (inclusion B r (n + 1)).comp (projection B r (n + 1))) := by
  sorry

end RationalPolynomialBar
