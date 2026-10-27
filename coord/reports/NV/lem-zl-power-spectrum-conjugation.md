## Worker report

The module `Sheaf.LinearAlgebra.PowerSpectrumConjugation` states
`LinearMap.power_spectrum_conjugation`, with its whole proof postponed by `sorry`.
No definitions, dependency repairs, or new nodes are needed. The original node is
unchanged except for its `lean` record.

The current blueprint source was read at
`literature/blueprint/latest/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
paragraph 1: after a finite constant extension, local Frobenius is a positive
integral power and powering preserves conjugation-stable spectra. This is the
source of the node's linear algebra statement, including algebraic multiplicities.

Hypothesis and clause correspondence:

- An algebraically closed field is `{K : Type u} [Field K] [IsAlgClosed K]`.
- A finite-dimensional vector space is `{V : Type v} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]`. The field and vector space have independent,
  explicitly bound universes, and there is no nonzero-space restriction.
- The endomorphism is `(A : V →ₗ[K] V)`. There is no assumption of invertibility,
  diagonalizability, semisimplicity, or nonzero determinant.
- A positive integral exponent is `(n : ℕ) (hn : 1 ≤ n)`; every positive integer
  has this representation. No characteristic restriction is imposed.
- The rank r is `Module.finrank K V`, used directly in the index type of
  `(α : Fin (Module.finrank K V) → K)`.
- Enumeration with algebraic multiplicities is
  `(hα : A.charpoly.roots = Finset.univ.val.map α)`. Mathlib's `Polynomial.roots`
  is explicitly the multiset of roots including multiplicities, and
  `Polynomial.count_roots` identifies its count with `Polynomial.rootMultiplicity`.
  `Finset.univ.val` has one occurrence for each index, so repeated eigenvalues
  remain repeated occurrences. This does not introduce a separability hypothesis.
- The first conclusion is `(A ^ n).charpoly = ∏ j, (X - C (α j ^ n))`.
- The second conclusion is `(A ^ n).charpolyRev = ∏ j, (1 - X * C (α j ^ n))`.
  The recorded dependency defines `charpolyRev` as `charpoly.reverse` and proves
  its equality with the matrix determinant `det (I - T A)`; no new determinant
  or reversal convention is introduced.
- Addition of algebraic multiplicities at collisions is stated explicitly as
  `∀ β : K, rootMultiplicity β (A ^ n).charpoly =
  Nat.card {j : Fin (Module.finrank K V) // α j ^ n = β}`.
  This counts all occurrences over the fiber of the power map, including
  distinct original eigenvalues with the same powered value. Grouping these
  occurrences by their original values gives precisely the node's multiplicity
  sum. `Nat.card` avoids adding decidable equality on the arbitrary field.
- The complex field isomorphism and the conditional nature of the reality claim
  are `∀ ι : K ≃+* ℂ, ... → ...` inside the last conjunct, so the unconditional
  polynomial formulas remain available over fields of every characteristic.
- The antecedent identifies `Finset.univ.val.map (fun j ↦ star (ι (α j)))`
  with `Finset.univ.val.map (fun j ↦ ι (α j))`. On ℂ, `star` is complex
  conjugation. Equality of multisets includes all multiplicities, not just support.
- The first conditional conclusion is the identical multiset equality with
  `α j ^ n` replacing `α j`.
- The last conditional conclusion is
  `∃ P : ℝ[X], P.map Complex.ofRealHom = (A ^ n).charpolyRev.map ι.toRingHom`.
  Thus the coefficientwise image of the reverse characteristic polynomial lies
  in ℝ[T], exactly as the node requires.
- In rank zero the index type is `Fin 0`; both displayed products are empty
  products equal to 1. This case is included, without another hypothesis.

Recorded dependency declarations read and used:

- `def-weil-characteristic-polynomial`: `LinearMap.charpoly`,
  `Mathlib.LinearAlgebra.Charpoly.Basic`; also read `LinearMap.charpoly_toMatrix`,
  `Mathlib.LinearAlgebra.Charpoly.ToMatrix`, and `Matrix.charpoly`,
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`.
- `def-weil-root-multiplicity`: `Polynomial.rootMultiplicity`,
  `Mathlib.Algebra.Polynomial.Div`. The public import
  `Mathlib.Algebra.Polynomial.Roots` supplies that declaration and the existing
  multiset of roots. Its definition and `Polynomial.count_roots` were read.
- `def-weil-reverse-characteristic-polynomial`: `LinearMap.charpolyRev`,
  `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`. Its definition,
  docstring, and `LinearMap.charpolyRev_toMatrix` were read; its public import
  also supplies the characteristic-polynomial declaration.
- Proof-only dependency `p-linear-triangular`:
  `Module.End.exists_le_map_le_finrank_eq_succ`,
  `WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable`.
  Its docstring and full signature were read, along with the complete invariant
  flag and triangular-basis consequences in the same module. Imported privately.
- Proof-only Mathlib leaf `lem-weil-pbc-block-triangular-determinant`:
  `Matrix.det_fromBlocks_zero₁₂`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`. Its docstring and signature
  were read. Imported privately, as required for proof dependencies.

The theorem docstring records every step of the node's proof: invariant flag and
adapted basis; block determinant induction; powered triangular diagonal and both
products; collision counts; permutation of conjugate occurrences and real
coefficients. Only the theorem proof is `sorry`.

Edge cases checked mathematically before writing:

- Rank zero: the root list is empty, characteristic and reverse polynomials are
  1, all multiplicity counts vanish, and the real witness is 1.
- A = 0 and positive rank: the characteristic polynomial is X^r, every powered
  root is zero, and the reverse product is 1. No full-degree assumption is made
  on the reverse characteristic polynomial.
- A Jordan block J₂(λ): no semisimplicity is required; its powered characteristic
  polynomial is (X - λ^n)^2, including λ = 0.
- diag(1, -1), n = 2: both occurrences map to 1, whose multiplicity is 2.
- Positive characteristic p with n = p: the counting formula does not use
  separability or divide by n; the complex clause is conditional on an isomorphism.
- n = 1: both products and the conjugation claim reduce to the original roots.
- diag(i, -i), n = 2: both powered occurrences are -1 and the reverse product
  is (1 + X)^2, with real coefficients.

Searches made (no existing declaration states the entire node):

- `msearch.py leanfinder`, query: "Characteristic polynomial roots with algebraic
  multiplicities of a positive power of an endomorphism and preservation of
  complex conjugation invariance". Eight hits: generalized/uniform eigenvalue
  definitions and `HasEigenvalue.pow`, `HasUnifEigenvalue.pow`; these do not
  provide algebraic multiplicities or either determinant product and reality.
- `msearch.py loogle`, query: `LinearMap.charpoly, HPow.hPow`. Eight hits:
  `charpoly_zero`, `charpoly_one`, `pow_eq_aeval_mod_charpoly`, nilpotence
  characterizations, and a determinant coefficient identity. None is this node.
- `msearch.py grep`, query: `charpoly.*pow|pow.*charpoly|roots.*pow`, subdirectory
  `LinearAlgebra`. Twenty-two hits: nilpotent special cases, polynomial
  evaluation modulo the characteristic polynomial, and finite-field Frobenius
  powers. None gives the general multiplicity and conjugation statement.
- `msearch.py leansearch`, query: "The characteristic polynomial of a power of
  an endomorphism has roots equal to powers of the eigenvalues with algebraic
  multiplicities and real coefficients if the original spectrum is conjugation
  invariant". Eight hits: characteristic polynomial definitions, eigenvalue and
  spectrum power results, and polynomial-power root results. Spectrum sets lose
  multiplicities; polynomial powers are a different operation.
- `rg` across `lean/WeilConjectures` and `lean/Sheaf` for
  `powerSpectrum|power_spectrum|charpoly.*pow|pow.*charpoly|roots.*pow|conj.*roots`,
  followed by a focused linear-algebra search. Existing trace-power formulas,
  exterior-power roots, and conjugation/weight operations are partial results,
  not the node. In particular `trace_pow_eq_sum_pow_roots_charpoly` only gives
  traces. Searches for the chosen theorem name found no collision.
- `grep -rn 'lem-zl-power-spectrum-conjugation' lean/WeilConjectures` returned
  no match. The upstream declaration index likewise has no chosen-name match.

No statement dispute or node fault was found. The first compile identified that
`IsAlgClosed` was available only through a private proof import; adding the direct
public import of `Mathlib.FieldTheory.IsAlgClosed.Basic` fixes the statement's
import visibility without changing its mathematical content.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
