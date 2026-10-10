# lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra

## Files

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra.json`: split into two steps; statement unchanged.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-dimension-inequality-quasi-finite.json`: new unsplit statement of Stacks Algebra Tag 00QF. No Mathlib match after three kinds of search.

## Source and split

Read `literature/stacks-project/algebra.tex`, Lemma Tag 00QG (`lemma-dimension-quasi-finite-over-polynomial-algebra`, lines 31291-31305), and its cited Lemma Tag 00QF (`lemma-dimension-inequality-quasi-finite`, lines 31266-31289) and Lemma Tag 00OP (`lemma-dim-affine-space`, starting line 27660). Tag 00QG bounds every local ring of the target using 00QF and the dimension of a polynomial-ring localization; the second step passes from local-ring bounds to a bound on every chain of primes of the target. The existing node `lem-weil-pbc-polynomial-ring-maximal-localization-dimension` states exactly the 00OP result used.

The first step cites `lem-weil-pbc-dimension-inequality-quasi-finite`, `lem-weil-pbc-proper-ideal-contained-in-maximal`, `lem-weil-pbc-localization-dimension-chains-below-prime`, and `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`. The second cites `lem-weil-pbc-spec-irreducible-closed-subsets-primes`, `lem-weil-pbc-localization-dimension-chains-below-prime`, and `def-kun-topological-krull-dimension`. These are all existing nodes except the new 00QF node. The proof uses the bound at an arbitrary prime of `T`; the spectrum can also be empty. The statement permits a noninjective polynomial map, which is valid because 00QF does not assume injectivity. I corrected the proof's target-algebra notation from `S` to the statement's `T`.

## Searches and blueprint

The item already recorded LeanSearch, LeanFinder, and Mathlib source grep searches for the 00QG dimension bound, with no match. For new 00QF I ran LeanSearch and LeanFinder and checked `Mathlib/RingTheory/QuasiFinite/Basic.lean` and `Mathlib/RingTheory/Ideal/Height.lean` in the read-only Mathlib source. Mathlib has `Algebra.QuasiFiniteAt` and `IsLocalization.AtPrime.ringKrullDim_eq_height`, but no declaration comparing the local dimensions of a quasi-finite source and base.

For B9, I searched the imported blueprint nodes by title, statement, source place, and tag for `00QF`, `00QG`, quasi-finite dimension, and polynomial quasi-finiteness. None states either new DAG node; the few broad hits concern other results. Both nodes therefore have `blueprint.same_as: []`. Their `blueprint.from` traces through the fibre-dimension neighbourhood and syntomic approximation nodes to step 7 of `thm-weil-pbc-finite-etale-lifting`; the item also records the relevant steps in `split_report.blueprint`.

## Checks

- `python3 tools/review_split.py lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra`: PASS, one new node.
- `python3 tools/check_dag.py`: PASS.
- No Lean code, unit file, or other node was changed. No WANTED source or Lean attachment.

## Review by J1

I read Algebra Lemmas 00QF and 00QG in `algebra.tex`, together with the 00OP polynomial-localization result. The item's hypotheses are exactly those needed by 00QF at every prime of `T`: finite type and quasi-finite at that prime. The source writes the polynomial map as an inclusion, but 00QF does not use injectivity, so the node's stated generality follows by the same proof. The new unsplit node reproduces 00QF with the contraction prime and both local-ring dimensions explicit; its source, four definition dependencies, three Mathlib searches, and B9 ancestor were checked. I searched the current DAG for 00QF and the local dimension comparison and found no duplicate.

Step 1 applies 00QF to each target prime, then uses the cited maximal-ideal existence, localization chain formula, and polynomial maximal-localization dimension statements to obtain `dim T_q ≤ n`. Step 2 uses the cited prime/irreducible-closed correspondence and the chain formula; taking the supremum is the cited topological Krull dimension definition. These citations state the facts used, including the direction of the prime-chain correspondence. For `n=0` every local ring is zero-dimensional, and an empty spectrum has dimension `-∞`, so the edge cases pass. I checked A-F of `coord/delivery-errors.md`: no uncited tag, hidden step, duplicate new node, off-route proof, or missing hypothesis remains. The worker corrected only the target-algebra notation `S` to `T`; I made no further mathematical correction.
