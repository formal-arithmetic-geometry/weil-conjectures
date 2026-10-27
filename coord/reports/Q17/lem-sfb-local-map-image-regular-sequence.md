# Stage-1 report: lem-sfb-local-map-image-regular-sequence

Group Q17, 2026-10-24. Direct delivery and self-review, as authorized in the dispatch brief.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-map-image-regular-sequence.json: statement, split; not a Mathlib leaf. Five proof steps, no new nodes, no new Mathlib leaves. The original statement, statement dependencies, source, chapter, unit and provenance are retained.
- citations.json: nine step/node citations, each quoting the cited node's complete statement verbatim.
- searches.jsonl: actual search-command output records. The item's earlier upstream searches remain in its JSON; fresh searches are appended.
- report.md: this report.

## Attachments

None. Searched the live project under lean/WeilConjectures for the exact blueprint docstring tag and for image/regular-sequence and local-map terminology. There is no declaration stating the whole item. The hits concern regular presentations, transport of already given regular sequences, or adjacent commutative algebra. No sorry declaration is treated as finished.

## WANTED

None. All mathematical sources used are in literature/stacks-project/algebra.tex.

## Audit and corrections

The item is true as written. There is no STATEMENT-DISPUTED correction and no statement weakening. Stacks Tag 06LC, lemma-find-sequence-image-regular, states the image-selection result; its proof invokes prime avoidance and the Cohen–Macaulay regular-sequence criterion, with dimension induction left implicit. I expanded that induction and its quotient hypotheses.

The induction proves the stronger depth-at-least-dimension version, which specializes to the given depth-equality assumption and matches both existing Cohen–Macaulay input nodes. This avoids silently requiring the quotient node to prove a depth equality that its statement expresses only as a lower bound. The source ring A is never assumed Noetherian and remains unchanged in the induction.

Read the chapter/unit records and SETUP's three blueprint levels. The inherited unit record is historical; in the latest blueprint the current thm-sf-ctf-stability statement/proof are filed under sec-six-functors/sk-thm-sf-kunneth-verdier. I read those current files. The old det-thm-sf-ctf-stability-direct-images detailed ancestor is absent there, consistently with the inherited null blueprint ancestor returned by tools/blueprint_refs.py ancestor. I retained the item's detailed provenance rather than inventing an ancestor or changing a unit/chapter route. This is the same local-algebra input 06LC, below the imported reduction chain.

## Not duplicates

No new nodes were created. The entire argument uses existing DAG inputs. Whole-blueprint searches for “prime avoidance”, “Cohen”, “regular sequence” and “minimal primes”, together with whole-DAG keyword/tag searches, found no second node stating the item. The regular-sequence search hits are definitions or purity statements, not source-image selection.

The useful facts already had nodes: lem-weil-pbc-prime-avoidance; lem-weil-pbc-noetherian-associated-primes-finite; lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes; lem-weil-pbc-cm-local-associated-prime-minimal; lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm; lem-weil-pbc-quotient-local-structure. I reused these rather than creating specialized copies. Even finiteness of minimal primes already exists as lem-sc-finite-minimal-primes-over-ideal, though this proof uses the finite associated-prime family instead and does not cite it unnecessarily.

## Mathlib searches

Ran the prescribed msearch.py with group Q17 and this item for all four services: LeanFinder, LeanSearch, Loogle and grep, plus a second LeanFinder phrasing and second grep pattern. Exact query strings and actual results are retained in searches.jsonl and the node's appended mathlib_searches entries. All returned successfully.

The first semantic query returned dimension formulas and localization transport, and the second returned localization, quasi-finite separation and an ideal/nonzerodivisor lemma. None chooses an element in a specified ring-map image. Loogle returned regular-versus-weakly-regular equivalences, depth suprema, permutation and regular-local instances. LeanSearch returned supplied-sequence transport and cons, among other dimension facts. I opened Mathlib/RingTheory/Depth/Rees.lean: its exists_isRegular_of_exists_subsingleton_ext chooses elements in an ideal using Ext vanishing, not from a ring-map image, so it is not a one-line specialization of the item. Grep's other hits were regular-sequence transport in Regular/Flat.lean. No leaf or attachment is asserted.

## Review by Q17

I reviewed delivery-errors B–E against the node and the sources, particularly whether every non-elementary use has a node and whether that node's statement, rather than its proof, supplies it.

For the item I read the statement and full proof of Stacks 06LC in algebra.tex. I also read 00DS (lemma-silly), 00LC (lemma-finite-ass), 00LD (lemma-ass-zero-divisors), 0BUS (lemma-CM-ass-minimal-support), and 02JN (lemma-reformulate-CM), plus the local-ring and local-map characterizations underlying the quotient-local-structure node. There are no new-node sources to review.

Step 1 states the simultaneous induction precisely, quantifying over both rings and the map. The cited regular-sequence definition says that the empty sequence is regular on a nonzero ring: all multiplication conditions are vacuous and the final quotient is B. This handles dimension zero without asking for an element avoiding its maximal ideal.

Step 2 uses exactly three cited statements. The associated-prime finiteness node applies because B is Noetherian and finite as its own module, generated by 1. The zerodivisor-union node shows that the family is nonempty, since 0 annihilates 1, and supplies the same notion of associated prime as the minimal-associated-prime node. The latter assumes a local Noetherian ring with finite dimension and depth at least that dimension; those are precisely the strengthened induction hypotheses. It concludes minimality, not an uncited dimension formula. Positive dimension then excludes the maximal ideal from this family by the prime-chain definition. This is not an application of a regular-ring lemma to a merely Cohen–Macaulay ring.

Step 3 cites prime avoidance in its full arbitrary-commutative-ring form, so it applies to A without Noetherianity. I checked its requirement r >= 1 using step 2. The inverse images of the associated primes are prime directly by the product test. The argument from containment of the image-generated ideal to containment of its radical is written using powers and primality. Thus the maximal ideal of A is contained in none of the inverse-image primes. Prime avoidance chooses a1 in that maximal ideal, and the cited zerodivisor-union statement then says its image acts injectively on B. Locality places that image in the maximal ideal of B. There is no assumption that the image itself is an ideal of B.

Step 4 applies the quotient-Cohen–Macaulay node with x in the maximal ideal and injective multiplication, established in step 3. Its statement gives Noetherianity, locality, dimension d-1 and depth at least d-1. I separately cite the quotient-local-structure statement for nonzeroness, the precise maximal ideal and locality of the quotient map. The source is still A. I wrote out both inclusions of the new radical equality, and the finite-sum description showing that the new extended ideal is the image of the old one. No identification is borrowed from a cited node's proof, and no flatness theorem is used.

Step 5 applies the dimension induction only after step 4 verifies all its hypotheses. It cites the regular-sequence definition and explicitly identifies each successive quotient, including the kernel calculation by lifting coefficients. This explains why the first injective multiplication and the quotient's tail sequence assemble to a regular sequence in B. The nonzero final quotient is inherited from the tail; at d=1 it is the nonzero first quotient. This is elementary assembly rather than a new lemma that restates the item's conclusion.

Small cases checked: d=0 uses only the empty sequence, including nonreduced Artinian local B. For d=1 the tail is empty and properness of xB is essential and verified by x lying in the maximal ideal. The zero ring is excluded by the item and quotient-local-structure. The associated-prime family is explicitly nonempty, so prime avoidance is never applied with an unsupported empty index set. The argument works for a source A that is not Noetherian; no lemma about associated primes of A is used. A field target is handled by the dimension-zero case, not by an attempted nonunit nonzerodivisor choice.

Both Cohen–Macaulay lemmas are generic commutative-algebra tools from another unit; split_report.tool_uses explains their purpose. The other imported tools are Mathlib leaves. Every proof dependency is used, every use is quoted in citations.json, and the union of the uses equals proof_deps. All five steps are below 2000 characters; the two elementary steps are induction setup/base case and explicit quotient/regular-sequence assembly. No lemma is hidden by a long step. No new nodes repeat a clause of the item, and no Lean, compiler or Lake command was run.

## Unfinished work

None in this stage-1 split. The existing non-leaf dependencies remain separate DAG work items; they were neither changed nor claimed proved by this delivery.
