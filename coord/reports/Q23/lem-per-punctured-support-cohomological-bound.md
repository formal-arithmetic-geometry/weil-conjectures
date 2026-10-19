# Q23: lem-per-punctured-support-cohomological-bound

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-punctured-support-cohomological-bound.json: statement, split by specialization of an existing more general DAG statement; not in Mathlib.
- citations.json: three verbatim statement excerpts for the two proof steps.
- report.md: this report.

No new nodes and no new Mathlib leaves. The pre-existing searches.jsonl and gabber.txt from the interrupted attempt were retained; the logged results were read and reused. No earlier split, report, or active delivery process was present when this continuation began.

## Attachments

None. Searches of the read-only slopmaster2 WeilConjectures tree by the exact blueprint id, punctured cohomology, and strict-local dimension terms found no declaration giving the item. The upstream master tree was also searched as reference material, without treating its declarations as finished proofs.

## WANTED

None. ILO Travaux de Gabber and the Stacks source are present.

## Corrections and reuse

The item statement is unchanged and agrees with ILO Expose XVII Proposition 3.2.1, printed p. 268: the closure is taken in X, coefficients are Z/ell, excellence and strict henselianity are assumed, ell is invertible, and neither constructibility nor normality is required.

The whole-DAG search found the existing lem-per-strict-local-etale-dimension-bounds, created under lem-per-normal-top-residue-class. Its first clause already gives this result with Z/ell^n coefficients. I reused it rather than creating another copy of Gabber's bound or of the source's affine-cover inputs. Unlike a new node that merely relocates the item, this is an already-existing common input for another branch, with additional supported and generic-point assertions. It has no proof dependencies and none of its statement dependencies reaches this item. Its finite-dimensional hypothesis was not silently omitted: Step 1 supplies it using the existing Mathlib leaf for Noetherian local rings and the spectrum dimension identification.

The same-unit citation is within sk-p-dl-a1-perverse. The generic ring finite-dimension fact is a Mathlib leaf, also declared in split_report.tool_uses for clarity. No unit or chapter route is changed. The unit record is not modified because this item is not its key statement. The ancestry remains the finite-coefficient potential-dualizing input in lem-per-artin-gabber-affine-curve Step 1, via the recorded pinned-extension chain.

Whole-DAG searches used the item id, punctured cohomology, support/cohomological bounds, ILO 3.2.1, and ringKrullDim/finite Noetherian local dimension terms. Blueprint searches used punctured, cohomological dimension, strict local, support, and Noetherian local finite Krull dimension. No imported blueprint node states this local excellent-scheme result; same_as remains empty. No new-node Stacks-tag duplicate pairs arise.

## Mathlib searches

The interrupted log's grep, LeanSearch, Loogle and LeanFinder results were retained and read. The first Loogle query names an unknown identifier and is recorded as unavailable, not evidence of absence. A second valid Loogle query, "cohomologicalDimension", returned no hits. The second LeanFinder phrasing about Gabber vanishing returned derived-category t-structure vanishing and structural-sheaf restriction results, not etale cohomological dimension. The earlier hits concern module support, etale loci and the definition of the etale topology. Their types concern different objects or require an ordinary t-structure bound already supplied as a hypothesis; they do not prove the item's geometric bound. No leaf is claimed. Every appended search entry copies the query and result from searches.jsonl, without reconstructing an unrun query.

## Unfinished work

Nothing in this one-level split. The already-existing strict-local dimension node remains a separate unsplit item; this delivery does not assert that its own proof is complete.

## Not duplicates

No new nodes. The item is explicitly routed through the more general existing lem-per-strict-local-etale-dimension-bounds. The maintainer may eventually merge this redundant special-case interface, but I have not changed any other node or its users.

## Review by Q23

I read ILO Expose XVII Proposition 3.2.1 and its proof on printed p. 268, and Proposition 3.2.2 on p. 269, in the retained PDF text. Proposition 3.2.1 explicitly treats arbitrary Z/ell sheaves and reduces to constructibles by filtered colimits, then to support closure, then uses an affine cover and Gabber affine Lefschetz. That verifies the scope and source of the existing shared cohomological input. This delivery uses that input's statement, not details of its proof. For the elementary finite-dimension preparation I read Stacks algebra.tex proposition-dimension, Tag 00KQ, and the paragraph giving the finite embedding-dimension upper bound; I also opened the existing Mathlib leaf and its instance in RingTheory/Ideal/KrullsHeightTheorem.lean:276, under the Noetherian commutative-ring variables. There are no new-node sources to audit.

For Step 1 I opened lem-weil-pbc-noetherian-local-finite-krull-dimension and def-weil-pbc-krull-dimension-ring. The former states exactly that a Noetherian local ring has nonnegative finite integer dimension; the latter explicitly identifies ring dimension with that of Spec R. The local scheme is Spec of its Noetherian local ring, so these statements supply every fact required to set d=dim X. The step is an elementary application of these cited statements, not an uncited use of Krull's height theorem.

For Step 2 I read the complete statement of lem-per-strict-local-etale-dimension-bounds. I checked S=X, closed point s there equals x here, exponent n=1, e equals our support parameter s, and d is the ambient finite dimension supplied in Step 1. Its hypotheses do not assume normality, integrality for this first clause, constructibility, or finite type over a field. Its coefficient sheaves and ordinary small-etale cohomology are the same as the item, and its closures are in S, hence in X. The vanishing conclusion, including equality at p=2s, is literally present in the quoted clause. The integral generic-point hypothesis belongs only to its final clause, which is unused. This is a direct specialization, marked elementary relative to the cited theorem; it adds no hidden comparison or devissage. Both steps are below 2000 characters.

For B1-B10, C1-C8, D1-D5 and E1-E7: no new nodes were created, no statements or notions were changed, all substantive facts are cited, the three citations are verbatim substrings checked against the opened statements, the cited generalization is an existing node rather than a newly renamed clause, and the finite-dimension hypothesis was explicitly discharged. No copied proof sketch is being substituted for a cited statement. The two proof steps contain neither an induction nor an unstated transport. All proof dependencies are exactly the union of uses. Definition and Mathlib-leaf citations need no route exception, and the only nonleaf theorem is in the item's own unit. No forbidden SGA route is used.

Small cases checked: if s=0, no point of the puncture can have closure dimension zero in a local scheme (the closure also contains its distinct closed point), so the support assumption forces zero stalks; vanishing includes H^0 consistently. If dim X=0, U is empty. If X is a strictly local trait and s=1, the first clause gives vanishing from degree 2, and does not falsely force H^1 to vanish. For larger s or support strictly smaller than s, the same first-clause substitution remains valid. None of these cases introduces a normality or constructibility assumption. The main correction during review was recognizing the existing more general node and checking its finite-dimension hypothesis instead of preparing redundant source-input nodes.
