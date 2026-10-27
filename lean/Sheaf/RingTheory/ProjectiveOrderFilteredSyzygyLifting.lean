module

public import Sheaf.RingTheory.PermissibleBasisChartData
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # One-level lifting of projective order relations

Source: Hironaka, Certain numerical characters of singularities (1970),
Lemma 17, pp.172–173, exact-relation consequence.
(blueprint: lem-trf-projective-order-filtered-syzygy-lifting).

The order spaces and dehomogenization are the existing constructions.
The affine variables are the nonzero labels of `Fin (r + 1)`; thus there
are exactly `r` affine variables. Completion is Mathlib's adic completion.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Hironaka

/-- An approximate relation at one filtration level among projective order forms
can be corrected to an exact relation in the completed local ring.

Source: Hironaka (1970), Lemma 17, pp.172–173, exact-relation consequence.
(blueprint: lem-trf-projective-order-filtered-syzygy-lifting).

Proof (the five steps of the DAG node):
1. For the empty family use the empty tuple. If `q = 0`, use zero coefficients.
For positive `q`, retain only indices with `e j ≤ q`; set the other output
coefficients to zero. Their approximation conditions have exponent zero, and
their contributions to the input sum already lie in the `(q + 1)`-st power.
2. A field is Noetherian since each ideal is zero or contains a unit.
The finite-type algebra and localization permanence theorems
`lem-weil-pbc-finite-type-algebra-noetherian` and
`lem-weil-pbc-localization-noetherian` show that the local ring is Noetherian.
Thus its maximal ideal is finitely generated (`def-weil-pbc-noetherian-ring`).
3. Apply `lem-weil-pbc-adic-completion-mod-power` at `q + 1` to represent each
retained coefficient by an element beta of the local ring. Compatibility of
quotient coordinates puts beta in the `(q - e j)`-th power and the resulting
sum in the `(q + 1)`-st power. Extension of ideals commutes with products,
so the extended powers are the powers of the extended maximal ideal.
4. Apply `lem-trf-projective-order-leading-syzygies`, with level `q`, to the
retained forms and coefficients beta. It gives homogeneous polynomial
relations and linear combinations of their evaluated coefficients agreeing
with beta modulo the `(q - e j + 1)`-st power.
5. Map these linear combinations into the completion and call them `v`.
Evaluation and the completion map preserve the polynomial relation identities,
so their weighted sum is zero. The difference from `u` is the sum of its
difference from beta and beta's difference from `v`, both in the required
power. Together with the zero choices at excluded indices this proves all
asserted congruences. -/
theorem projective_order_filtered_syzygy_lifting
    {k : Type u} [Field k] (r b q : ℕ)
    (p : PrimeSpectrum (MvPolynomial {i : Fin (r + 1) // i ≠ 0} k))
    (e : Fin b → ℕ) (φ : Fin b → MvPolynomial (Fin (r + 1)) k)
    (he : ∀ j : Fin b, 1 ≤ e j)
    (hφ_ne : ∀ j : Fin b, φ j ≠ 0)
    (hφ : ∀ j : Fin b, InOrderSpace r p (e j) (φ j))
    (u : Fin b → AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal))
    (hu : ∀ j : Fin b, u j ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
        (algebraMap _ _) ^ (q - e j))
    (hsum : (∑ j : Fin b, u j *
      algebraMap (Localization.AtPrime p.asIdeal) _
        (algebraMap _ (Localization.AtPrime p.asIdeal)
          (MvPolynomial.dehomogenizeX k 0 (φ j)))) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
        (algebraMap _ _) ^ (q + 1)) :
    ∃ v : Fin b → AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal),
      (∑ j : Fin b, v j *
        algebraMap (Localization.AtPrime p.asIdeal) _
          (algebraMap _ (Localization.AtPrime p.asIdeal)
            (MvPolynomial.dehomogenizeX k 0 (φ j)))) = 0 ∧
      ∀ j : Fin b, u j - v j ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
          (algebraMap _ _) ^ (q + 1 - e j) := by
  sorry

end Hironaka
