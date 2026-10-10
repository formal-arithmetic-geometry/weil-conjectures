Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-leray-lowdegree.json`: split item; no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-pqf-leray-five-term.json`: statement-only child; Mathlib searches found no match.
- `citations.json`: one entry for each citation used by the item's proof step.

Attachments: none. No sorry-free declaration in `WeilConjectures/` states this scheme-cohomology five-term sequence; the nearby source declarations define Grothendieck edge maps but do not prove this item.

WANTED: none.

## Not duplicates

lem-pqf-leray-five-term vs lem-weil-pbc-first-quadrant-row-collapse: the existing node assumes every positive-q row vanishes and proves collapse to an isomorphism in all degrees; the new node has no row-vanishing hypothesis and states the five-term exact sequence involving E_2(0,1), the transgression, and H^1/H^2.

lem-pqf-leray-five-term vs def-sp-filtration: the existing node defines finite filtrations and their graded pieces; the new node is a theorem extracting exactness of the first five terms of a spectral sequence from its filtration and differentials.

The imported proof was too compressed to identify the generic five-term exact-sequence result it used. I made that result an explicit unsplit child node and retained the Leray and cohomology dependencies. The statement itself was checked on the zero sheaf and on an identity morphism: the exact sequence reduces to the expected identity/zero cases, and vanishing of `R^1 f_* F` makes the middle `H^0` term zero, so exactness gives an isomorphism in degree one.

## Review by M1

I read the item source recorded in `dag/nodes/sec-abelian-varieties/pqf-lem-leray-lowdegree.json` and the imported proof, then read the statements of `pqf-lem-leray`, `pqf-def-cohomology`, and `lem-sp-grothendieck-edge-maps`. The first cited node supplies the Leray E2 page and its abutment, exactly the two identifications used in the item. The cohomology definition states that H is the right derived functor of global sections and that higher direct images are the right derived functors of pushforward, which supplies the notation identification. The edge-map node states the canonical bottom and left edge maps and their functoriality, which is the map identification used when instantiating the five-term child.

The new child node states the generic five-term exact sequence, including the edge and transgression maps, and is deliberately unsplit because it is the one level below the item. I ran LeanSearch (unavailable), LeanFinder, Loogle, and Mathlib grep for both the item and the child; the available searches found only generic page or homology infrastructure, with no convergence/abutment five-term theorem. I checked the R1-vanishing conclusion directly from exactness: `H^0(Y,R^1 f_* F)` is zero, so the preceding map is surjective as well as injective. The citation quotes are verbatim substrings of the four cited node statements.

What I could not finish: no Lean implementation was requested or written at stage 1, and the source repository has no exact declaration to attach.

## Second reading by M1

- Item statement: checked the Leray low-degree sequence against the imported blueprint node and [pqf-lem-leray]; verdict: hypotheses and terms agree, and the $R^1$-vanishing specialization is a valid exactness chase.
- Step 1: checked each use against the verbatim statements of [pqf-lem-leray], [pqf-def-cohomology], [lem-pqf-leray-five-term], and [lem-sp-grothendieck-edge-maps]; verdict: every non-elementary identification is cited, with no unstated use of a node proof.
- New node [lem-pqf-leray-five-term]: checked its self-contained first-quadrant, abelian-category, convergence, filtration, edge, and transgression hypotheses against [def-sp-abelian], [def-sp-convergence], and [def-sp-filtration]; verdict: one statement-only unsplit child is necessary because no existing node states the generic five-term extraction.
- Small cases: the zero and identity spectral sequences reduce to zero or identity maps; when $E_2^{0,1}=0$, exactness gives the expected $H^1\\cong E_2^{1,0}$ consequence.
- Searches: rechecked the existing-node grep and the recorded LeanFinder, Loogle, LeanSearch, and Mathlib grep searches; verdict: no Mathlib five-term theorem or duplicate DAG node.

Changes made: corrected the child source to Stacks Homology Lemma 0132 (label `lemma-first-quadrant-ss`), made its convergence and map hypotheses explicit, and filled the item's blueprint provenance. The source lemma supplies finite filtration and convergence; the five-term display is the standard total-degree extraction, so this limitation is recorded rather than presented as a verbatim Stacks statement.

## Source error

Stacks Lemma 0132 states first-quadrant convergence and finite filtrations but does not print the five-term exact sequence verbatim. The child records the sequence as the standard extraction from that lemma and the edge-map construction; no stronger source claim is made.
