# Stage-1 delivery: lem-sfb-integral-lattice-cubical-contraction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-lattice-cubical-contraction.json`: item, statement unchanged, split into eight explicit elementary calculations. No Mathlib match.
- `citations.json`: verbatim statement quotations for all five step/node citation pairs.
- `report.md`: this report.
- Local evidence only: `searches.jsonl` (search command log) and `finite-check.txt` (finite signed-chain calculation).

New nodes: 0. New Mathlib leaves: 0. The two reused definition nodes are already Mathlib leaves.

## Attachments

None. Searched the item id, cubical, integral lattice, lattice, contraction, and Koszul terminology in the project source under `lean/WeilConjectures/`. No declaration states the whole item; declarations about integral representation lattices concern different objects. No Lean was written or compiled.

## WANTED

None. No unavailable document is invoked. This is explicitly an agent-written coordinate proof rather than an attribution of the contraction to a source that does not state it.

## Original material and route

The sandbox contained no earlier node, report, citations or search log at startup. The live item was unsplit, with empty proof and no project declaration. Copied its current JSON, retained every imported/maintainer field and its existing search records, kept its statement exactly, and appended the searches actually run for this item. The current statement is true, including rank zero and negative coordinates; no STATEMENT-DISPUTED correction was necessary.

Read GOAL.md, the worker and stage-1 contract, SETUP.md's three levels, delivery-errors B--E (including the merged historical copy), the chapter record, the assigned unit record, and the current blueprint's direct-image proof paragraph (3). This item is a lower-level algebraic ingredient of the already split discrete-lattice resolution. Its proof does not change the geometric direct-image route or the unit theorem. It is not the unit key node, so no unit realization record is changed. The ancestor utility returns None for this inherited created-node chain; the existing `blueprint.from.node: null`, via list, and precise place are retained. Whole-blueprint searches for cubical, contracting homotopy, lattice and Koszul did not identify an equivalent blueprint node; `same_as` remains empty.

## Mathlib assessment

Read every returned search hit description and the actual sources of the plausible candidates: `RepresentationTheory/Homological/Resolution.lean` (in particular the standard simplicial resolution, lines 160 onward, and its forgotten homotopy equivalence at 249), `Algebra/Homology/AlternatingConst.lean` (the periodic alternating complex and homotopy equivalence at 232), and `Algebra/Homology/Augment.lean` (augmentation construction). A bar resolution has different basis sets in every degree and is not the finite cubical resolution; its comparison with this complex would require a theorem. The alternating constant and Dold--Kan constructions concern other complexes. The Loogle hits describe operations on an already supplied homotopy; the second LeanFinder phrasing returned the bar differential, partial sums and unrelated signed sums. None is an exact statement or one-line specialization of the item. The exact queries, results, service outcomes and dates are appended from the command's JSONL log, not invented. Existing inherited searches are preserved.

## Not duplicates

No new nodes are created, so there are no new/existing-node pairs requiring a tag comparison. The item itself is the integral-chain input, not the larger derived-invariants statement `lem-sfb-discrete-lattice-koszul-resolution`. The latter cites this item and is never used to prove it.

## Review by NJ

I read Stacks `more-algebra.tex`, Tag 0623 (`definition-koszul-complex`) and its preceding alternating boundary formula, and Tag 062F (`lemma-regular-koszul-regular`) with its proof, checking their tag/label correspondence in `tags/tags`. They give the Koszul setup and regular-sequence acyclicity, respectively. Neither asserts the required integral nonequivariant contraction. I therefore wrote and checked a finite coordinate construction and marked `proof_origin.by` as agent. I do not use regular-sequence acyclicity, tensor homotopy transport, cellular homology, projective resolutions, or any SGA theorem as an unstated lemma.

Step 1 uses exactly the basis clause of `def-weil-pbc-free-module` to extend finite formulas and the chain-complex/homology definition of `def-weil-pbc-module-chain-complex-homology` to interpret the result. I opened both node files in full. A free module's unique finite expansions give the universal extension by substituting basis images. For each distinct pair of face directions I checked that the two removal orders have exponents differing by one, with identical translated terms. The degree-zero boundary is explicitly set to zero, and augmentation of a one-face boundary is 1-1.

Step 2 uses no external result. Resetting one coordinate defines `p_i`; if that coordinate is present in the face set, its own boundary terms become identical and cancel, and all other faces are killed. If it is absent, coordinate reset commutes with the other translations. This proves the chain-map and commuting properties on the supplied basis, rather than assuming a tensor identification.

Step 3 again uses only `def-weil-pbc-free-module` for the extension of finite basis formulas. The signed summation convention separately covers positive, zero and negative endpoints. I checked both telescoping identities at -1 and 0 as well as general negative endpoints. Every image has finite support. In top degree every coordinate is present, so each insertion operator is zero.

Steps 4 and 5 are the verification for the actual complexes in this item, not appeals to a general homotopy lemma. In the absent-coordinate case I checked both comparisons j<i and j>i, including how removing j changes the insertion exponent. The i-face telescopes to the original cell minus the reset cell. In the present-coordinate case only the removed-i face survives; the two upper endpoints differ by one and their path difference is precisely the original cell. The prefactor and boundary signs cancel. These two cases exhaust every basis cell and require no boundedness, flatness or equivariance assumption beyond the statement.

Step 6 composes the coordinate chain maps and inserts the already verified coordinate homotopies. Moving the differential past each preceding reset map gives the displayed finite telescoping sum. The product of all resets kills every positive-degree cell and sends every vertex to the origin. Thus it equals exactly the statement's e, with no comparison complex or unidentified map involved. The empty product and sum give the rank-zero conventions.

Step 7 uses the explicit kernel/image meaning of the quoted chain-complex homology definition. For a positive-degree cycle, or a degree-zero element in the augmentation kernel, the identity from step 6 displays its preimage h(x). Augmentation is surjective because its section sends 1 to the origin. This proves exactness, including at the final copy of the integers and at top degree. The rank-zero group has a singleton basis, so its identification with the integers and identity maps are explicit.

Step 8 uses the free-basis description, not an external theorem on group rings: translation of each boundary term agrees with first translating the input; each fixed-I subgroup has the lattice basis with its regular translation action; partitioning the basis by I gives the direct sum. The index set of subsets is finite. A translation of the chosen origin need not be the origin, so no equivariant contraction is assumed. This checks the last clauses as well as the warning about h and s.

Every nontrivial cancellation and identification is written in the proof; there is no unproved auxiliary assertion hidden in a long step. The eight steps range from 545 to 723 characters, below 2000. All are elementary finite computations in the item itself using its two definition nodes; extracting coordinate identities with their own unchanged hypotheses as new nodes would merely fragment this calculation. Each uses list equals what is cited, the proof-dependency list is their union, and `citations.json` quotes were checked as literal substrings of the node statements. Definition nodes are Mathlib leaves and are not off-route theorem tools. No other node or maintainer field is edited.

As an independent small-case check, I evaluated the written boundary, every H_i, every p_i and the assembled h as sparse integral chains on all 1,111 basis cells of ranks 0 through 3 whose coordinates lie between -2 and 2, for every coordinate subset. Boundary squared, every coordinate homotopy identity and the assembled contraction all passed, including negative endpoints and top-degree cells. This finite check supplements the general basis calculation; it is not its proof.

B--E self-review: no new-node statement or duplicate/relabelling issue arises; the statement introduces all objects and keeps its definition links. The two cited statements say exactly what their steps use, with no use of the proofs of those nodes. The dependency graph contains only those reused leaves, hence no new cycle. Every formula is finite, all indices and degree-zero conventions were checked, no hypothesis was imported from a larger source, and the source's limited scope is stated explicitly. Nothing remains mathematically unfinished.

## Unfinished work

None in the split. Required server dry run and delivery results are reported by the delivery command.
