## Worker report

The module `Sheaf.RingTheory.SymmetricPolynomialCocycleNormalForm` states
`MvPolynomial.symmetric_polynomial_cocycle_normal_form`, with its proof `sorry`.
It adds no definitions and changes only the item's `lean` field. The integer
coefficient expression defining c_p is expanded directly in the conclusion.

Clause-by-clause correspondence:

- An arbitrary field k is `{k : Type u} [Field k]`, for explicit arbitrary universe u.
- Prime positive characteristic p is `(p : ℕ) (hp : p.Prime) [CharP k p]`.
  Primality already implies positivity, so p = 0 and p = 1 are excluded exactly
  as in the node. No perfectness or algebraic closedness assumption occurs.
- The polynomial f in k[X,Y] is `f : MvPolynomial (Fin 2) k`.
  Variables 0 and 1 are X and Y respectively.
- `hX` substitutes `(T,0)` into f, as an identity in `Polynomial k`;
  `hY` substitutes `(0,T)`. These are the two normalization conditions.
- `hsym` substitutes `(Y,X)` into f and equates the result to f.
- `hcocycle` is an identity in `MvPolynomial (Fin 3) k`, whose variables
  0, 1, 2 are X, Y, Z. Its four substitution vectors, in order, are
  `(Y,Z)`, `(X+Y,Z)`, `(X,Y+Z)`, `(X,Y)`, with signs +, -, +, -.
  All these are polynomial identities, rather than identities on k-points.
- `r : ℕ` encodes the integer r ≥ 0. The list a_0,...,a_r is
  `a : Fin (r + 1) → k`, and the sum runs over all of `Fin (r + 1)`.
- `b : Polynomial k` and `b.eval 0 = 0` encode the required b and b(0) = 0.
- The displayed c_p is `-∑ j ∈ Finset.Ioo 0 p, ...`. Its summand is
  `C ((p.choose j / p : ℕ) : k) * X 0 ^ j * X 1 ^ (p - j)`.
  This performs exact natural division on the nonnegative integer binomial
  coefficient before casting to k. For prime p and 0 < j < p this is exactly
  the integer quotient in the node; the external negative sign is preserved.
- `C (a i) * (...) ^ (p ^ (i : ℕ))` is a_i c_p^{p^i}.
- The three `Polynomial.aeval` terms evaluate b at X, Y, X+Y and give
  the coboundary with signs +, +, -. The final equality has precisely the
  sum of Witt terms plus this coboundary.

Dependencies read and used:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs`; the full class extends
  `CommRing` and `DivisionRing`, as required.
- def-weil-polynomial-ring: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`,
  publicly supplied by `Mathlib.Algebra.Polynomial.AlgebraMap` (which supplies
  `Polynomial.aeval` used in the statement).
- def-weil-pbc-mv-polynomial-ring: `MvPolynomial` and its universal evaluation
  `MvPolynomial.aeval` from `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`.
  Read also `MvPolynomial.algHom_ext`, the uniqueness clause; it is not needed
  to express this theorem. `.Eval` publicly provides `.Basic`.
- def-pc-field-characteristic: `CharP`, `Mathlib.Algebra.CharP.Defs`.
  Read also `ringChar`, `CharP.existsUnique`, and `ringChar.spec`; explicit
  `CharP k p` is the recorded notion appropriate to a specified p.
- All proof dependencies are these same four nodes, already publicly imported.
  `Fin.VecNotation` supplies the substitution tuples and `Nat.Choose.Basic`
  supplies the binomial coefficients in the actual statement.

Source checked: the local Milne Algebraic Groups PDF, printed pp.308-309 and
316. The formula immediately before Lemma 15.26 is
f_1 = (X^p + Y^p - (X+Y)^p)/p, giving exactly the negative mixed-term sum.
The lemma classifies symmetric cocycles modulo coboundaries; the node requests
its existence clause. The theorem's docstring carries all eight steps of the
reviewed coefficient-induction proof, including signs and Frobenius descent.

Edge cases checked before writing: f = 0 admits r = 0, a_0 = 0, b = 0;
r = 0 still has one coefficient via Fin 1. At p = 2 the inner sum consists
only of j = 1 and equals c_2 = -XY. At p = 3 it gives
c_3 = -(XY^2 + X^2Y). Coefficients are never divided in k. Normalizations
are polynomial equalities and remain meaningful over finite fields. Imperfect
fields are included, and no p-th roots of coefficients occur. Both variable
sets are finite index sets encoding exactly the two and three indeterminates,
without restrictions on the coefficient universe. No statement fault found.

Searches for existing statements:

- msearch.py leanfinder: "Every normalized symmetric polynomial additive two
  cocycle over a field of characteristic p is a finite sum of Frobenius powers
  of the Witt carry cocycle plus a polynomial coboundary". Eight hits, including
  `WittVector.polyOfInterest`, `xInTermsOfW`, `frobeniusRotationCoeff`,
  `wittPolyProdRemainder`, and Frobenius polynomial lemmas; none states the
  cocycle classification.
- msearch.py loogle: `"MvPolynomial", "cocycle"`; zero hits.
- msearch.py grep: `symmetric.*cocycle|cocycle.*symmetric|Witt.*coboundary`;
  zero hits.
- msearch.py leansearch: "Symmetric normalized polynomial additive two cocycle
  classification in positive characteristic by Witt cocycles modulo
  coboundaries". Eight hits, including abstract group cohomology cocycles,
  Witt ring and quotient constructions, `WittVector.addIsPoly₂`, and
  `WittVector.wittAdd`; none gives the normal form of all polynomial cocycles.
- rg of lean/WeilConjectures and lean/Sheaf for
  `polynomial.*cocycle|cocycle.*polynomial|wittCarryPolynomial|symmetric_polynomial_cocycle_normal_form`:
  only unrelated projective-space Čech cocycles and tensor algebra cocycle text.
  grep for the item's exact id in lean/WeilConjectures: no hits.

The previous worker ending concerned an unchanged stage-1 item. The current
coord/brief-stage2.md §0 explicitly resolves that handoff: this node is queued
at stage 2 and has no Lean record. The accepted split is preserved in full.

## Second reading by Q78

Author's self-check under the direct-delivery worker brief; independent review
is the maintainer's responsibility. Re-read the node and the complete Lean
signature. The two normalization maps have codomain k[T], the symmetry map
has codomain k[X,Y], and all four cocycle terms have codomain k[X,Y,Z]. This
preserves polynomial equalities even for finite k. The prime binder and CharP
instance state exactly prime positive characteristic. Fin (r+1) includes the
last index r, and the exponent is p^i, including p^0 = 1. The division is
before the cast; the outer minus matches Milne. The conclusion is associated
as the Witt sum plus b(X) plus b(Y) minus b(X+Y). There is no uniqueness claim
or perfection assumption. No mismatch required a statement change.

Validation: scompile.py compiled both the isolated sandbox module and the named
library module successfully (3.4 s and 4.2 s). The cocycle codomain is explicitly
annotated as `MvPolynomial (Fin 3) k` to fix the coefficient ring.
