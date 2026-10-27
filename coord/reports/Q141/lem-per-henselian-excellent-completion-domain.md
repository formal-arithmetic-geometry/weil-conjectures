# Stage-1 delivery: lem-per-henselian-excellent-completion-domain

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-excellent-completion-domain.json`: split item, six proof steps, statement unchanged. New Mathlib searches appended to the earlier searches.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The dependency lemmas needed for the proof already exist. `prepare.py` and `searches.jsonl` are sandbox working records, not proposed repository files.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for excellence/henselianity together and domain/completion together. The hits are curve-branch, DVR-completion, and reduced-completion results; none proves this item for arbitrary excellent henselian local domains. In particular reduced completion does not imply domain completion.

## WANTED

None.

## Corrections and route

The item statement is correct and unchanged. There was no existing split in the sandbox. Read the latest blueprint ancestor `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md`, the chapter record and the perverse-unit record. This is a commutative-algebra input in the established finiteness/duality branch, not a change of the unit's Fourier/perverse argument.

The substantive source is Illusie–Laszlo–Orgogozo, Expose I Proposition 6.2 and Corollary 6.3(i)-(ii), printed p.14 (PDF page 20), read directly by pdftotext. The source passes to the finite local normalization and its normal local completion and then uses the inclusion of the original completion. The split writes out both locality and that inclusion. Excellence of the normalization allows us to use the existing normal-completion clause of `lem-per-henselian-normal-completion-preparation`; we do not apply a normal-ring result directly to the possibly nonnormal original ring.

The generic tools from other units are declared in `split_report.tool_uses`: quasi-excellence implies Nagata, finite henselian algebra decomposition, permanence of excellence, and completion of a finite extension. They supply commutative-algebra inputs the perverse unit does not itself state. The remaining off-unit statement citations are Mathlib leaves.

## Mathlib and duplicate searches

Read the item's earlier recorded search results, retaining them. Ran fresh searches through the required msearch command: two LeanFinder phrasings, Loogle `"AdicCompletion", "IsDomain"`, LeanSearch for analytic irreducibility of an excellent henselian domain, and grep for excellence/analytic irreducibility/unibranchness. All services responded. The results are Hensel lifting, complete implies henselian, and valuation-specific completions; no exact/generalized match. Loogle returned no hits; grep's sole excellence hit is an unrelated prose adjective in Lie theory. The exact tool/query strings and returned hits are recorded in the item and logged in searches.jsonl.

Before considering a new node, searched the whole DAG by normalization, completion, henselian finite algebra, excellence/Nagata, and the relevant tags. Blueprint searches for henselianity, normalization and `completion is a domain` found no duplicate blueprint statement for this item. The ancestor command returned `lem-per-artin-gabber-affine-curve`. All candidate auxiliary statements were found in existing nodes, so no nodes were created and no duplicate-pair exclusions are needed.

## Review by Q141

I read delivery-errors B through E, including the repeated sections, and checked the actual statements of every cited node against the use made of it; citations.json copies those statements verbatim. I also read the local Stacks statements/proofs 034L (integral closure in a normal domain), 032F and 032R (Japanese/Nagata), 07QV and 07QU (excellence), 04GH (finite henselian algebra decomposition), 00MB (exactness of completion), 07N9 (finite-extension completion), and 0C23 (normal completion). The ILO statement and proof are the source for this item; there are no new nodes requiring additional source review.

Step 1 uses `def-exc-excellent-ring` only for excellent implies quasi-excellent, `lem-exc-quasi-excellent-nagata` exactly for Nagata, and `def-weil-pbc-nagata-ring` with the zero prime of the given domain. `def-weil-pbc-japanese-domain` explicitly permits the trivial finite field extension, so it gives finiteness of the normalization. `def-weil-pbc-integral-closure` supplies its construction as a subring of the fraction field and its integrality, while `lem-weil-pbc-integral-closure-finite-extension-normal` states normal-domain status, not merely existence of an integral closure. No finiteness of normalization is inferred just from the integral-closure definition.

Step 2 uses the full statement of `lem-weil-pbc-finite-over-henselian-local-product`, which gives local factors and contraction of their maximal ideals. The hypotheses are precisely henselian local A and finite A-module B. I explicitly dealt with zero factors and the empty product and proved that there is only one nonzero factor using a pair of complementary idempotents in a domain. This elementary product argument is part of the step, not a new node.

Step 3 uses the finite-type definition and writes out why module generators are algebra generators. `lem-exc-finite-type-localization-excellent` then applies with multiplicative set {1}; `def-exc-excellent-ring` supplies Noetherianity. This avoids assuming the normalization is excellent or Noetherian without a cited statement.

Step 4 uses only the standalone completion clause in the statement of `lem-per-henselian-normal-completion-preparation`: “For any normal excellent Noetherian local domain B ...”. It does not use its henselization construction or any fact buried in that node's proof. Normality, excellence, Noetherianity and locality of our B have all been established before the clause is applied. This clause is strictly more restricted than the current item in its normality hypothesis; it does not restate the assertion for a nonnormal A.

Step 5 uses `lem-weil-pbc-completion-exact-finite-modules` on the displayed finite-module short exact sequence, with Noetherian base A, and identifies the induced injection coordinatewise as a unital ring homomorphism. The quotient B/A is finite because the images of any module generating set of B generate it. The statement of `lem-weil-pbc-integral-prime-over-maximal-maximal` applies because B is integral over A by its construction in step 1, and ensures that every prime above m is maximal. Locality of B then leaves exactly n, whose contraction was already supplied in step 2. `lem-weil-pbc-completion-finite-extension` explicitly identifies the completion for the base ideal with the product of completions at primes above it, with the induced local maps. With this unique prime it gives the required comparison with the n-adic completion. I kept the mB and n topologies distinct until this theorem was applied; neither equality of these ideals nor levelwise injectivity of A/m^j into B/m^jB is asserted. The localizations at the two maximal ideals invert units, hence are the original rings, an elementary identification written in the step.

Step 6 is the explicit algebra argument that an injective unital map into a nonzero domain makes its source a nonzero domain. It needs no separate lemma or source assumption. Both nontriviality and absence of zero divisors are checked, matching both clauses of the item's definition of domain.

For small cases, if A is a field, m=0, its normalization B=A and both completions equal A, so the argument still applies. If A is already normal, the construction has B=A and the injection is the identity after completion. For a nonnormal excellent henselian domain, we never infer normality of A. The zero ring is excluded by the original domain hypothesis; the zero-factor discussion in step 2 therefore cannot produce an empty normalization. Positive characteristic, inseparable residue extensions and arbitrary dimension cause no added hypothesis: none of the tools used assumes perfection, separability, rank one or dimension one. Henselianity is used essentially to obtain one local normalization factor.

Each non-elementary inference has the cited statement that supplies it. No new node is an elementary observation or a clause of the item, since no new nodes are proposed. Every step is shorter than 2000 characters. I have neither written Lean nor invoked any compiler, Lake or build tool, and all local writes are confined to the assigned sandbox.

## Unfinished work

None in this one-level split. Existing dependency nodes retain their own proofs/status. Required server dry run and push follow this report.
