## Worker report

The new module `Sheaf.Algebra.Lie.Sl2DividedStraightening` states
`Algebra.sl2_dividedPower_straightening`, with the single expected `sorry` proof.
The natural-language statement is unchanged. The only added statement dependency is the landed
`def-sfb-kostant-integral-form`, whose module already supplies the exact divided-power and
falling-binomial functions used here. No new notion or dependency repair is needed.

Hypothesis and clause correspondence:

- The unital associative rational algebra is `(A : Type u) [Ring A] [Algebra ℚ A]`.
  `Ring` is associative and unital without imposing multiplicative commutativity. The explicit
  universe permits arbitrary sizes, and no `Nontrivial A` is assumed.
- The three elements are `(E F H : A)`. Mathlib's ring bracket is definitionally
  `x * y - y * x`, as `LieRing.of_associative_ring_bracket` states. Thus
  `hEF : ⁅E, F⁆ = H`, `hHE : ⁅H, E⁆ = 2 * E`, and
  `hHF : ⁅H, F⁆ = -(2 * F)` are exactly the three displayed associative identities.
  Multiplication by the ring numeral `2` is twice the element; its negative is `-2F`.
- `Algebra.rationalDividedPower x j` is `(1 / (j.factorial : ℚ)) • x ^ j`.
  `Algebra.rationalBinomial x j` is the same rational scalar acting on
  `((List.range j).map (fun k : ℕ ↦ x - (k : A))).prod`.
  Both existing definitions are from `Sheaf.Algebra.Lie.KostantIntegralForm`; their complete
  signatures and docstrings were read. The list product has increasing indices and its
  empty value is one. Factorials are inverted in ℚ, never in the noncommutative algebra.
- Arbitrary nonnegative exponents are `(m n : ℕ)`. The conclusion's left side is exactly
  `rationalDividedPower E m * rationalDividedPower F n`.
- `∑ t ∈ Finset.range (min m n + 1), ...` sums each integer from zero through
  `min m n` inclusively. The ordered summand is
  `rationalDividedPower F (n - t) *
  rationalBinomial (H - (m : A) - (n : A) + 2 * (t : A)) t *
  rationalDividedPower E (m - t)`.
  All shifts are ring subtraction after casting; in particular, no truncation is used in
  `H-m-n+2t`. Natural subtraction occurs only in the exponents, with `t ≤ m,n` throughout
  the summation range. Multiplication retains the required negative / toral / positive order.
- There are no finite-dimensionality, nilpotence, faithfulness, nonzero-triple, domain or
  commutativity hypotheses. Mathlib's `IsSl2Triple` is deliberately not assumed: its field
  `h_ne_zero` excludes a case this statement expressly allows.

Dependency declarations used:

- `def-wf-lie-algebra` is a Mathlib leaf. Its recorded
  `Mathlib.Algebra.Lie.OfAssociative` supplies `LieRing.ofAssociativeRing`,
  `LieAlgebra.ofAssociativeAlgebra` and the commutator identity
  `LieRing.of_associative_ring_bracket`. Read these definitions and their docstrings, along
  with `LieRing` and `LieAlgebra` in `Mathlib.Algebra.Lie.Basic`. The other clauses of that
  definition bundle (ideals, representations, solvability) are not needed for this item.
- Added landed dependency `def-sfb-kostant-integral-form` records module
  `Sheaf.Algebra.Lie.KostantIntegralForm`, main declaration `LieAlgebra.kostantIntegralForm`,
  with `Algebra.rationalDividedPower` and `Algebra.rationalBinomial` in `lean.declarations`.
  Its full source was read. Those functions apply to arbitrary rational algebras, not just
  universal enveloping algebras. No replacement definition was written.
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic` provides the finite-sum notation/API.
  The sole original proof dependency is also `def-wf-lie-algebra` and is publicly imported
  because it is already a statement dependency.

Edge cases checked before writing:

- `m = 0` or `n = 0`: `range 1` contains only zero, both binomial and zero divided powers
  are one, and the formula is the identity for the remaining divided power.
- `m = n = 1`: the two terms are `F * E` and `H`, giving precisely `EF = FE + H`.
- `m = 1, n = 2`: the second term is `F * (H-1)`, agreeing with the telescoping identity.
  For `m = 2, n = 1` it is `(H-1) * E`, so the toral placement and shift agree as well.
- `E = F = H = 0` is allowed. In positive total degree every term vanishes; at
  `m = n = 0` both sides are one. A subsingleton algebra is also allowed.
- Noncommutative algebras, infinite-dimensional algebras, nonnilpotent elements, and negative
  integer shifts of `H` remain within the binders. The denominator factorial is always a
  nonzero rational, and the empty falling product is one.

Sources read: the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`,
and Milne's `literature/milne-algebraic-groups_iAG2017.pdf`, printed pp. 508–510
(PDF pages 520–522). Milne supplies the rank-one/admissible-lattice motivation, not the explicit
normal-ordering proof; the theorem docstring accurately attributes and carries all eight
steps of the DAG's associative calculation, including both summation endpoints. The node's
full Steinberg-source WANTED note is unchanged. No statement fault or dispute was found.

Searches made (all automated Mathlib searches used the prescribed `msearch.py Q28` wrapper):

- LeanFinder: “In an associative rational algebra an sl2 triple satisfies the divided power
  straightening formula E^m/m! F^n/n! with binomial coefficients in H”. Eight hits included
  `RootPairing.GeckConstruction.isSl2Triple`, `IsSl2Triple`, and the three primitive-vector
  action identities. None states the universal associative normal-ordering identity.
- Loogle: `"Ring.choose"`. Twelve hits include `Ring.choose`, its zero/one evaluations and
  binomial product identities. These are binomial API, not the sl2 straightening theorem.
- Mathlib grep: `straightening|IsSl2Triple|divided` in `Algebra/Lie`. Sixteen hits are sl2
  triples and root-system uses; no matching theorem. Read `Sl2.lean`'s structure signature
  to verify that its nonzero hypothesis cannot be imposed here.
- LeanSearch: “binomial coefficients Ring.choose for noncommutative rational algebras
  factorial scalar inverse”. Eight hits include `Ring.choose`, `Ring.multichoose` and
  `Ring.choose_eq_smul`. Read `Mathlib/RingTheory/Binomial.lean`: none is the desired
  normal-ordering statement. The project already uses its exact explicit rational falling
  product function, so that existing project API is reused.
- `rg` over `lean/WeilConjectures/Algebra` and `lean/Sheaf/Algebra` for divided powers,
  factorials, binomials and straightening found `KostantIntegralForm.lean`, the distinct
  rank-two straightening theorem, and the PBW consumer. Full-project `rg` for
  `rationalDividedPower|rationalBinomial|sl2_dividedPower|sl2_divided_power` confirmed the
  helpers' owner and found no duplicate of the new theorem name. The prescribed upstream
  `grep -rn "lem-sfb-sl2-divided-straightening" lean/WeilConjectures` had no hit.
- DAG searches for divided powers/binomials located `def-sfb-kostant-integral-form` and its
  recorded declarations. This existing landed node was added directly to `stmt_deps` under
  brief-stage2 §5; no new node was introduced.

Validation: the delivered module is compiled through `scompile.py`; the wrapper's dry-run
preflight and final delivery results are recorded below when completed.

`scompile.py` passed both its sandbox and library-module checks, with no errors or warnings.
`deliver2.py --no-push` printed `OK (dry run)` and confirmed the complete packet passes the
server preflight and compiles. The packet has exactly the report, the item's node JSON,
and its Lean module. Delivery is submitted with the prescribed wrapper.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
