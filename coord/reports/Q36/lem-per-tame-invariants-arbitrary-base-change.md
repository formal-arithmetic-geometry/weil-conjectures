# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-tame-invariants-arbitrary-base-change.json`: statement, split into five proof steps; full assertion not found in Mathlib. No statement change.
- `citations.json`: one verbatim statement quotation for each node cited by each proof step.
- `searches.jsonl`: actual search-command records; existing item search records are preserved in the node.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Three existing Mathlib leaves are reused.

## Attachments

None. Searched the read-only slopmaster2 project for the blueprint id, Reynolds, tame invariants, invariants/baseChange, averaging and invariant terminology, including its RepresentationTheory and LinearAlgebra directories. No project declaration states every clause. Upstream master was searched for the exact tag and relevant base-change names too; it supplies no attachment.

## WANTED

None. The relevant Stacks text and pinned Mathlib sources are present. The full Reynolds extension is an explicit agent proof, not claimed to be the statement of Tag 0BRH.

## Findings and corrections

The imported statement is true as written. Stacks 0H36 (`remark-when-iso`) observes invertible-order invariants modulo an ideal; 0BRH (`lemma-base-change-invariants`) proves an algebra comparison under flatness and gives only weaker conclusions in general. Neither tag by itself states this item's arbitrary-module, arbitrary-base-change theorem. I read both actual source passages, verified their tag/label pairs in `tags/tags`, and supplied the Reynolds retraction argument explicitly with `proof_origin.by = agent`.

The existing `lem-weil-pbc-idempotent-endomorphism-image-base-change` was considered and rejected as a citation: its ambient module is finite free, whereas this item makes no finite-generation, freeness or flatness assumption on M. Its proof cannot be used as if its statement covered arbitrary modules. Instead I wrote the two tensor identities directly from the existing universal property.

The current main-20261015 ancestor text contains the affine perverse assertion; the historical Step 3 route recorded in this item's ancestry is expanded in the existing `lem-per-gabber-abelian-stage-toric-chart`. Its Step 3 uses precisely the projection, and Step 10 uses the algebra comparison for a potentially nonflat base. This split supplies both without any SGA route or coefficient-category identification. No unit record is changed: this item is not a unit key statement.

## Not duplicates

No new nodes. Whole-DAG searches for Reynolds, averageMap, idempotent/tensor, tags 0H36 and 0BRH, and the relevant filenames were read; `blueprint_refs.py search invariants` found 14 blueprint nodes, none stating this scalar-extension assertion. A whole-blueprint tensor-product search identified the generic tensor interfaces already in the DAG. The only same-tag algebra-invariants items are geometric quotient variants and this item's existing parents; none is replaced or duplicated.

## Unfinished work

None at stage 1. No Lean was written, no compiler or Lake command was run, and all authored files are in this item's sandbox. Server dry run and direct delivery follow this report.

## Review by Q36

I read `more-algebra.tex` around labels `remark-when-iso` (0H36) and `lemma-base-change-invariants` (0BRH), `algebra.tex` Section 00CV including Lemma 00CX and its quotient construction, the unit and chapter records, the main-20261015 ancestor, and the relevant toric-chart parent steps. I also opened all three cited node statements and pinned Mathlib `RepresentationTheory/Invariants.lean:125-145`. The latter supplies the averaging projection only; it does not justify marking the full item Mathlib. Two semantic phrasings, Loogle patterns and logged grep searches were run. The results are retained accurately, including the command's single-file grep output format, without treating those malformed file fields as declaration locations.

Step 1 checks the group action is A-linear, finite and of unit order exactly where the sum and division are used. Left multiplication permutes G, so the average is fixed; on a fixed vector its d summands cancel the inverse of d. Thus the image, identity and idempotence clauses are proved in the step itself. This is two finite-sum calculations, not a new hidden lemma, and needs no theorem-node citation.

Step 2 uses `lem-weil-pbc-module-base-change-universal-property`: its statement explicitly constructs the unique B-linear extension with formula b tensor m maps to b u(m). I checked its hypotheses: A and B are commutative, both tensor targets are B-modules with compatible A-action, and r is A-linear by Step 1. It gives J and R, not an exactness theorem. `def-weil-pbc-module-tensor-product` explicitly states bilinearity and generation by pure tensors, so the action laws and averaging formula are checked on generators. Unit order survives every unital A-algebra map, including to the zero ring. There is no flatness hypothesis to verify or import.

Step 3 uses that same definition's pure-tensor generation to extend the displayed identities RJ = id and JR = e_T. I checked the domains: R starts on T, J starts on U, alpha is J corestricted to T^G, and the inverse is R restricted to T^G. The latter is valid because e_T fixes T^G by Step 1 applied over B. This is a direct two-identity check, so elementary is justified even though it finishes the module clause. It never tensors an unsupported claim of injectivity and never assumes M is finite free.

Step 4 again cites the definition's pure-tensor generation. Equivariance of f ensures f restricts to invariants; the displayed averaging identity checks its compatibility. An A-algebra map v gives the map b tensor m maps to v(b) tensor m by bilinearity. Both naturality squares are displayed on generators, with the semilinear nature of the change B to B' allowed; no tensor-associativity comparison is silently asserted. Agreement of the isomorphisms implies agreement of their inverses too.

Step 5 uses `lem-weil-pbc-algebra-tensor-base-change-universal-property`, whose statement says exactly that A-algebra maps from C^G into a commutative B-algebra extend uniquely to B-algebra maps out of B tensor C^G with the specified pure-tensor formula. It also constructs each extended group automorphism; its inverse is obtained from g inverse and checked on tensors. I verified closure of invariants under products and the unit using algebra automorphisms, and the fact that B is fixed using its scalar action. The tensor definition identifies the resulting underlying linear map with alpha. The inverse preserves multiplication by the explicit preimage computation in the step, not because averaging is multiplicative (it generally is not).

For small cases I checked G trivial, M zero, B zero, arbitrary direct sums (no finite-rank step occurs), and nonflat reduction A = Z[1/2] to B = A/3. With the order-two sign action on M = A/9 both invariant modules vanish; with the trivial action on the nonflat module M = A/3 the comparison is the identity on B tensor M. For the algebra clause take C = (A/3) times (A/3), with the swapping involution and the same nonflat B: invariants are diagonal and both sides are B, so neither B nor C needs flatness. The same diagonal calculation works over a ring with nilpotents. To check why invertible order is essential, over A = Z with sign action on M = Z and B = F_2, M^G is zero but the base-changed action is trivial, so the conclusion would fail without that hypothesis.

I checked delivery-errors B--E against the actual files: no new statement-only nodes or duplicate clause nodes are needed, no use of a cited proof in place of its statement occurs, every non-elementary interface is cited, and all actual scalar, linearity and algebra hypotheses were matched above. The five steps are all shorter than 2000 characters. I corrected the tempting finite-free citation and made the extended algebra actions explicit. The item statement, source field and inherited blueprint ancestry are preserved.
