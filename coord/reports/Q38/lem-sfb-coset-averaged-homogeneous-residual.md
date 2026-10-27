# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-coset-averaged-homogeneous-residual.json`: statement, now split into nine finite-sum arguments; no exact project attachment or Mathlib match found.
- `citations.json`: verbatim statement quotations for both citations in the proof.
- `report.md`: this report. `searches.jsonl` was generated only by the required msearch commands.

There are zero new nodes and zero new Mathlib leaves. All original search records and metadata are retained; the searches run by Q38 are appended with their actual results. No Lean was written or compiled, and no repository or launcher file was changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, cosets, averaging, and homogeneous residuals. The discrete-module induction file has a right-coset permutation and a trace, but not this statement for arbitrary topological vector spaces and arbitrary given tuple-chain maps.

## Literature

Read the chapter record `sec-six-functors-basics`, the unit `sk-thm-sf-ctf-stability`, and the current `main-20261015` direct-images proof, especially paragraph (3). The last is context for the tame-kernel expansion; it does not assert this auxiliary lemma. The parent node's source explicitly calls its argument agent-formulated and asks for an exact literature reference. This delivery therefore honestly has `proof_origin.by = agent`. It proves the auxiliary claim directly by finite sums rather than attributing it to a nonexistent blueprint proof.

Read the full statements of `def-weil-pbc-free-module` and `def-weil-l-adic-numbers`; also inspected Algebra `item-free-module` (Stacks Tag 00C2) in `literature/stacks-project/algebra.tex` and the coefficient convention in the blueprint's `def-weil-finite-field-fiber.md`.

WANTED: a published reference for the parent scalar tame-kernel finite-evaluation construction, including the normalization of a given tuple-chain homotopy, for this item and `lem-sfb-bounded-finite-evaluation-rectangle-replacement`. No reference of that precision is present in the stated source. No proof step here is deferred to it.

## Source error

STATEMENT-DISPUTED: the notation `B_{-1}(G) = Z[emptyset]` literally denotes the free abelian group on an empty indexing set, which is zero, whereas the displayed augmentation intends the basis vector of the empty tuple. By the cited basis definition the free group on the empty set contains only its empty sum; it cannot contain a nonzero augmentation generator. Repaired the notation to `B_{-1}(G) = Z[{()}]` and `partial[x] = [()]`, explicitly naming the unique empty tuple. This is the intended rank-one augmentation and changes no substantive hypothesis or conclusion.

No other statement correction was necessary. In particular no openness or normality of H, prime-to-ell index, completeness, or degree-(n+1) endomorphism was added. The existing chain-map and augmentation hypotheses are retained, even though the evaluation identity uses only the assumed chain-homotopy identity in degree n.

## Not duplicates

No new nodes were created. Whole-blueprint searches for `homogeneous cochain` and `coset`, and whole-DAG searches for alternating deletion, truncated homotopies and normalized coset averaging, found no exact equivalent of this item. Read the related statements `lem-sfb-finite-coset-homogeneous-averaging`, `lem-sfb-equivariant-continuous-cochain-prism`, `lem-sfb-topological-homogeneous-cochain-coordinates`, `lem-sfb-bar-resolution-cochains`, `lem-sfb-scalar-cochain-averaging-primitives`, `lem-sfb-homogeneous-polynomial-augmented-resolution`, `lem-sfb-equivariant-prefix-finite-chain-homotopy`, and `lem-sfb-ordered-coset-finite-chain-projection`. The first constructs transfer using an open subgroup of a compact group; the prism has a particular substitution homotopy; the prefix/projection nodes construct the integral maps assumed here. None is needed as a black box for evaluating already-given maps. Turning the few-line computations into new nodes would violate the elementary-node rule.

The ancestor command reports `None` for this inherited auxiliary chain; retained the existing blueprint ancestry and its specific source place. The item is not the unit's key theorem, so no unit realization file is edited.

## Review by Q38

I checked B through E against the statements and the actual calculations. There are no new statement-only nodes to audit, no restated-clause nodes, no relocation of the whole proof, and no hidden invocation of transfer or cohomology invariance. Every argument is written in the item; each step is elementary because it checks a formula from the hypotheses or prior steps in a few lines. The longest step is under 700 characters, well below the long-step threshold.

Step 1 cites the free-module node for exactly its unique finite basis expansion, which makes additive evaluation well-defined. It then proves the boundary/differential equality on generators. Step 2 cites no external theorem: its two signs for each omitted pair cancel; it separately checks continuity and invariance by commuting coordinate deletion with translation. Step 3 cites the l-adic-number node only for the explicitly stated characteristic-zero field property: the nonempty finite coset set has positive cardinal, so that integer has an inverse. Continuity uses only finite composition, addition and fixed scalar multiplication. Both cited clauses were copied literally into citations.json; neither definition is used as a citation for an unstated theorem.

Step 4 checks the direction of the cosets carefully: right multiplication permutes H-backslash-G and yields sa = h_s pi_a(s), with h_s in H. Left diagonal H-invariance then removes h_s, and reindexing proves G-invariance. Its inverse permutation comes from a inverse. Step 5 explicitly interchanges the finite deletion and coset sums, and separately counts the m equal summands when L is G-invariant. Neither step uses normality or continuity of a choice of representatives.

Step 6 uses exactly the finite continuous tuple expansions and the H-equivariance assumed for Q and A. Equivariance is needed only for their linear extensions, not for individual summand maps. Step 7 evaluates the GIVEN chain-homotopy identity; the partial-Q_n term is zero because delta F is zero on every generator and hence on every chain. Its remaining term is precisely delta(UF), by step 1. Applying delta and the cancellation in step 2 proves cocyclicity of WF without an A_(n+1). Step 8 applies the independently defined averaging operator to that equality and uses steps 4 and 5, including averaging in degree n+1 for the cocycle calculation. Step 9 uses support in E to kill every evaluation, even without the cocycle hypothesis, and displays both final finite evaluation lists and their coefficients k/m. This is also the direct proof of linearity and independence from V.

Small cases checked: n=1 gives UF of degree zero, with Q_0 and Q_1 both available and no negative-degree cochain required; H=G gives a single representative and the identity average on invariant functions; H={1} in a finite nonabelian group still has the stated right permutation, including nonnormal intermediate subgroups; an index divisible by ell remains invertible in Q_ell; zero coefficient space and zero summands cause no exception; E empty forces A_n=0 and the same formulas hold conditionally on the given hypotheses. All sums are finite, so neither completeness nor separation of V occurs. Repeated basis tuples may be retained without equality tests; their integer coefficients simply add.

I corrected only the empty-tuple notation and supplied the absent proof. The two statement dependencies are definitions, so their different units introduce no change of route. No SGA source is used. The remote search index returned ContinuousCohomology names absent from the pinned local Mathlib; these were not claimed as verified matches. Other hits concern low-degree cocycles or homology maps and do not state the item.

## Unfinished work

None in the mathematical split. Maintainer review remains independent of this signed self-review.

## Validation

The required `deliver.py Q38 lem-sfb-coset-averaged-homogeneous-residual --no-push` exited successfully: `OK (not pushed)` at `dd0d2399bb0`, with server preflight passed. The dry run had fully exited before the push invocation. The delivery command rechecks the final report and split before pushing.
