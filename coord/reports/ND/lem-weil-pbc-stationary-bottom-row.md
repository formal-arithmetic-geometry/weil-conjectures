# Stage-1 report: lem-weil-pbc-stationary-bottom-row

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-stationary-bottom-row.json — statement item, split; no whole-item Mathlib match. Statement and existing source/search history retained; four explicit proof steps added.
- citations.json — verbatim statement excerpts for every cited node in every proof step.
- searches.jsonl — actual msearch output log; five fresh searches, including a second semantic phrasing, read before deciding the whole item is not a Mathlib leaf.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. The proof reuses lem-weil-pbc-short-complex-zero-homology, already a Mathlib leaf.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for stationary, bottom-row, iCyclesIso and asIsoHomologyπ terminology. CategoryTheory.SpectralSequence.nonempty_abutment_iso_row_zero in WeilConjectures/CategoryTheory/SpectralSequenceNatRowZero.lean:40 concerns a natural-bidegree first-quadrant spectral sequence with an abutment and gives a Nonempty abutment isomorphism. Its local stationary induction is useful corroboration, but its declaration does not state this item's integer-bidegree canonical maps, late-page comparisons and recursion. It is not an attachment. No compiler was run.

## WANTED

None. Sources used are present locally.

## Findings and changes

The live item had a statement and search history but no proof. Its statement is correct; no STATEMENT-DISPUTED correction was necessary. In fact, its all-page row-support assumption implies zero adjacent differentials at every bidegree already for r >= 2, which immediately implies the requested weaker late-page assertion. The proof explicitly distinguishes a zero middle object from the two zero neighbors on the bottom row. No convergence, existence of infinite limits, or abutment hypothesis is used.

The Mathlib searches returned the separate page-homology and cycles/homology isomorphisms, not this entire statement as a one-line specialization. Read Mathlib/Algebra/Homology/SpectralSequence/Basic.lean:37-47, ShortComplex/LeftHomology.lean:486-493, and ShortComplex/Homology.lean:1147-1156. The existing short-complex node already packages the exact two invertibility facts required. Creating another node for those facts, for finite composition of isomorphisms, or for the support inequalities would duplicate existing material or turn an elementary step into a node.

Blueprint duplicate searches: tools/blueprint_refs.py searches for stationary, stationary bottom, bottom row, zero differentials, and degenerates; whole-DAG keyword and declaration searches; direct reading of the item and short-complex leaf. No other blueprint node states this precise canonical stationary comparison statement. The nearest blueprint ancestor is lemma-weil-pbc-cancellation, as reported by the ancestor tool. The item retains its precise from.place and same_as = []. The latest blueprint chapter and sk-thm-reduction unit, together with the latest cancellation statement and proof, were read. This remains the local row-collapse calculation inside cancellation, without changing the chapter or unit route. Every proof dependency is either an existing definition leaf or the short-complex leaf of this very unit.

The old historical brief mentions coord/dag-sync.md; that file is absent from this shared clone. The current direct-delivery instructions identify the live shared DAG and library explicitly and suffice for this task.

## Unfinished work

None within this stage-1 item. No new subordinate items were necessary. No Lean was written and no compiler, Lake, local preflight or local DAG/review checker was invoked.

## Not duplicates

No new nodes. The exact short-complex calculation is reused from lem-weil-pbc-short-complex-zero-homology rather than recreated. The parent first-quadrant-row-collapse node additionally proves propagation and an abutment comparison; this item assumes all-page support and proves only stationary comparisons, so it does not use its parent or create a cycle.

## Review by ND

I read Stacks homology.tex at Tag 011N, label definition-spectral-sequence, including the paragraph allowing a starting page r_0 and specified next-page isomorphisms; Tag 011O, label definition-limit-spectral-sequence, including the subsequent stationary-page observation; and Tag 0BDV, label lemma-relate-boundedness. The last is only background for eventual stabilization: it is not substituted for the explicit support argument, and its omitted proof is not used. I also read the newest blueprint cancellation proof, part (1), whose spectral-sequence row-collapse sentence is the precise source obligation recorded by the item. Since I expanded the elementary calculation and finite composites, rather than claiming that the source gives this exact multi-clause lemma verbatim, proof_origin is agent with the local Stacks source identified. There are no new nodes requiring additional sources.

For Step 1 I reopened def-sp-abelian and verified that its statement supplies a zero object. The only fact taken from it is the defining uniqueness of maps to and from that object. For q nonzero the middle object is zero, making both maps zero even if a neighboring entry could be nonzero. For q = 0, the actual incoming second coordinate is r - 1 and outgoing second coordinate is 1 - r, respectively positive and negative for r >= 2. Both vanish by the stated hypothesis, without needing a first-quadrant assumption beyond what the item gives. This is an elementary case calculation, not a hidden vanishing theorem.

For Step 2 I reopened lem-weil-pbc-short-complex-zero-homology. Its statement defines precisely the kernel inclusion i and homology quotient pi used here, and explicitly asserts that g = 0 makes i invertible and f = 0 makes pi invertible. Step 1 supplies exactly those hypotheses in the abelian category of the item. I checked both facts against the Mathlib source lines quoted above. I reopened def-sp-spectral-sequence and verified that its statement supplies specified homology-to-successor isomorphisms with the correct direction. Composing the three displayed invertible maps therefore gives the stated t, and the explicitly written reverse composite has both inverse identities by cancellation. The citations file quotes those actual statements. Canonicity here is relative to the specified page identifications and canonical kernel/homology maps, not independence of changing the spectral sequence's input identifications.

Step 3 cites no new fact. It defines finite composites, gives the induction base and successor for invertibility, and obtains compatibility from associativity and inverse-pair cancellation. The same comparisons work in reverse order by inversion. Thus the statement about all late pages is justified by actual maps and a composition rule, rather than an unexplained assertion that they are canonically the same. No infinite categorical construction is needed.

Step 4 specializes Steps 1–3 at (n,0) and identifies the recursion with that very finite composite. I checked n + 2 >= 2 and n + 2 > max(n,1), including n = 0 where the stable-page identification is the empty composite. No additional abutment or finiteness assumption enters. I tested r = 2 on the bottom row (incoming row 1 and outgoing row -1), p < 0, q nonzero including q = r - 1 and q = 1 - r where one neighbor could lie on row zero, and the zero category. For the off-row examples the zero middle object still kills both maps, as Step 1 requires.

Against delivery-errors B–E: no statement-only children, duplicate nodes, missing notion definitions, new unverified Mathlib leaf claims or source-by-section-number claims were introduced. Every non-elementary external fact is a cited statement that I read, with the exact hypotheses checked above; no cited proof internals, parent dependence, or changed route is used. The proof totals 2094 characters; its longest step is 590, so no step over 2000 characters conceals a lemma. The corrections were to the missing argument, not to the statement. Required dry run and push results are recorded below after execution.
