## Worker report

The module defines `MvPolynomial.maximalChain_height_difference`.  It uses
`MvPolynomial (Fin n) k` for the polynomial ring `P`, with `k : Type u` a field
and `n : ℕ`.  A prime ideal `q` is represented by an ideal with the typeclass
hypothesis `[q.IsPrime]`; its height is Mathlib's `Ideal.height`, whose prime
case is the supremum of lengths of strict prime chains below it.  The first
conclusion `q.height ≤ (n : ℕ∞)` is the bound `ht(q) ≤ n`.  The second
conclusion quantifies a prime `p`, the inclusion `p ≤ q`, a finite chain
`c : Fin (t+1) → Ideal P`, and requires every chain member to be prime,
endpoints `p` and `q`, strict adjacent inclusions, and the condition that no
prime lies strictly between adjacent members.  Its length conclusion is
`(t : ℕ∞) = q.height - p.height`, the natural-number length coerced to
`ℕ∞` so it can equal Mathlib's extended-natural height difference.

The dependency declaration is Mathlib's `MvPolynomial` abbreviation from
`Mathlib.Algebra.MvPolynomial.Basic` (the dependency node is a Mathlib leaf).
`Ideal.height` is from `Mathlib.RingTheory.Ideal.Height`; for prime ideals its
docstring identifies it with `Order.height` on the prime spectrum, i.e. the
supremum of strict chain lengths below the prime.

Edge cases checked: `n = 0` is admitted (`Fin 0` and the zero-variable
polynomial ring); `t = 0` is admitted (`Fin.last 0` is the sole endpoint and
the adjacency/maximality conditions are vacuous); `p = q` is admitted; and
heights are allowed to be `ℕ∞` even though the theorem bounds prime heights.
The chain's maximality is exactly the node's clause (no intermediate prime for
each adjacent pair), with endpoints fixed, and no extra maximality hypothesis
was added.

Searches made: `msearch.py ... leanfinder "maximal chains of prime ideals
polynomial ring field height difference"` returned only polynomial height
lemmas and no chain-difference theorem; `msearch.py ... loogle "Ideal.height,
LTSeries, IsMaxChain"` returned no matches; `msearch.py ... grep
"catenary|height.*chain" RingTheory` returned no matches.  `rg` over
`WeilConjectures/` and `lean/Sheaf` found no declaration of this theorem;
nearby modules only use the node as a theorem dependency.  The Mathlib source
for `Ideal.height` and its prime-height characterization was read directly.
No statement correction or disputed statement was needed.

## Earlier second reading (a previous round; superseded)

The Lean signature was reread against every clause of the node.  `k`, `n`, and
`P` are the same objects; `[q.IsPrime]` and `[p.IsPrime]` express that both
ideals are prime; `p ≤ q` is ideal inclusion; `c` has exactly `t+1` entries,
its endpoints are `p` and `q`, all entries are prime, every adjacent inclusion
is strict, and the displayed existential negation excludes an intermediate
prime.  The first conjunct is the stated height bound, and the final equality
uses the canonical `ℕ∞` coercion for the node's height difference.  No mismatch
was found.

## Second reading by K1

I independently opened the node copy, its sole statement dependency
`def-weil-pbc-mv-polynomial-ring`, the delivered Lean, and the Stacks algebra.tex
source on the server (local literature/stacks-project is absent). Read the whole
section introduction and the statements/proofs at labels lemma-dim-affine-space,
proposition-finite-gl-dim-polynomial-ring, and
lemma-dimension-height-polynomial-ring (00OP, 00OQ, 00OR). The section assumes a
field, with no characteristic or algebraic-closure restriction. The official
pages https://stacks.math.columbia.edu/tag/00OR and
https://stacks.math.columbia.edu/tag/00OP were also checked. The node's additional
height bound follows from 00OP as its proof explains; it is retained.

Object/hypothesis/conclusion list, with the Lean rendering and verdict:

1. Field k: `{k : Type u} [Field k]`; exact, arbitrary universe and characteristic.
2. Nonnegative integer n: `(n : ℕ)`; exact, includes zero.
3. Polynomial ring P = k[x_1,...,x_n]: `MvPolynomial (Fin n) k`; exact finite
   reindexing of the dependency's family of variables. Opened Mathlib Basic's
   `MvPolynomial` abbreviation: `AddMonoidAlgebra k (Fin n →₀ ℕ)`, the stated
   finite sums of monomials, not a different polynomial notion. Also read its
   `algHom_ext` and Eval's `aeval`, `aeval_X`, `aeval_unique` signatures; the
   recorded dependency is usable and no dependency module is needed.
4. Prime q of P: `(q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime]`; exact.
5. Height as supremum of finite strict prime chains ending below q:
   `q.height`; exact for prime q. Read Ideal.Height's definition and
   `PrimeSpectrum.height_eq_orderHeight`, and Order.KrullDimension's `height`
   definition (supremum over LTSeries with last at most q). The infimum over
   minimal primes in general Ideal.height reduces to this height for a prime.
6. First conclusion ht(q) ≤ n for every q: `q.height ≤ (n : ℕ∞)` as the first
   conjunct under arbitrary q; exact, no finiteness assumption added.
7. Prime p contained in q: `∀ (p : Ideal ...) [p.IsPrime], p ≤ q →`; exact.
8. Every finite chain with t inclusions: `∀ (t : ℕ) (c : Fin (t + 1) → Ideal ...)`;
   exact, with `(∀ i, (c i).IsPrime)` for all its members.
9. Endpoints p and q: `c 0 = p → c (Fin.last t) = q →`; exact.
10. Strict adjacent inclusions: `∀ i : Fin t, c i.castSucc < c i.succ`;
    exact ideal strict inclusion. Transitivity places all members between p and q.
11. Maximality between fixed endpoints: `∀ i : Fin t, ¬ ∃ r : Ideal ...,
    r.IsPrime ∧ c i.castSucc < r ∧ r < c i.succ`; exact exclusion of an
    intermediate prime at each adjacent pair. No condition requiring p minimal
    or q maximal in the entire spectrum is added.
12. Length conclusion: `(t : ℕ∞) = q.height - p.height`; exact. The first
    conjunct bounds both heights (apply it also to p), so extended-natural
    subtraction expresses precisely the stated finite height difference.

Edge cases: n = 0 permits the empty variable set and P = k, height zero.
t = 0 gives one chain member, equal endpoints, and vacuous adjacent conditions;
p = q is therefore covered, with length and height difference zero. The zero
ideal is allowed and prime since P is a domain; the zero ring is not a field
and is outside the node's scope. An empty chain is not between two specified
endpoints, so Fin (t+1) excludes no intended case. No scheme or characteristic
hypothesis is present. Universe u is declared and all variables are bound;
the finite index set needs no additional universe. No extra Noetherian,
finite-height, finite-dimensional, or algebraically-closed instance appears.

Independent searches (different wording from the worker): msearch leanfinder
`equidimensional affine space saturated prime intervals length codimension
difference` returned eight quotient-dimension and regular-sequence dimension
lemmas, none a saturated-chain height-difference statement. msearch loogle
`MvPolynomial, Ideal.height` returned zero hits. msearch grep
`saturated|equidim|catenar` in RingTheory returned five unrelated localization
saturation occurrences. Direct rg with `catenar|saturated.chain|maximal.chain|
height.*covby|covby.*height` in pinned Mathlib RingTheory, source
WeilConjectures, and project lean/Sheaf found only Ideal.height_le_iff_covBy,
its Krull-height-theorem use, and references in nearby project dimension and
CM-chain modules, not this statement. The proposed full declaration name was
also absent in the source, project library, and dag/lean_names_upstream.json.
Thus no existing exact declaration replaces this delivery; all notions used
are already canonical Mathlib notions.

Mismatch and repair: the theorem signature is correct and unchanged. Its
original docstring compressed six DAG proof steps into a short sketch, omitting
the height-bound argument and the construction/saturation of a height-realizing
chain (H8). Expanded it to all six steps with their dependency node names,
including the bound via a containing maximal ideal, the empty regular sequence,
and concatenation in the upper-prime localization. Added the standard copyright,
license, and author header (H9). There are no definitions, no hollow data,
no proved helper statements, and the single theorem proof remains `sorry`.
No new nodes, dependency modules, or statement correction were required.
The node lean.statement remains verbatim the unchanged theorem signature.

## Reviewer fix (R-pmc1346)

The delivered statement was faithful, but encoded the chain as a bare
`c : Fin (t + 1) → Ideal P` with separate primality, strictness and
no-intermediate-prime hypotheses. Restated with the chain form of the landed
siblings (`finiteTypeDomain_ringKrullDim_localizationAtMaximal`,
MaximalChainLengthOfDepth): `c : LTSeries (PrimeSpectrum P)` with
`c.head.asIdeal = p`, `c.last.asIdeal = q` and `∀ i : Fin c.length,
c i.castSucc ⋖ c i.succ`; the conclusion is `(c.length : ℕ∞) = q.height - p.height`.
`CovBy` in `PrimeSpectrum P` is by definition `a < b ∧ ∀ r, a < r → ¬ r < b`,
exactly the node's saturation clause; primality and strictness come from the
series. Height bound, heights (`Ideal.height` in `ℕ∞`), `MvPolynomial (Fin n) k`
and `{k : Type u} [Field k]` unchanged, matching C1's landed sibling
PolynomialQuotientDimensionAtPointHeightDifference.
