## Files written

- `dag/nodes/sec-six-functors/lem-coef-cubical-open-box-pair.json`: item split, no new nodes, no Mathlib leaves.

## Attachments

None.

## WANTED

WANTED: Hovey, *Model Categories*, Lemma 2.4.13 proof, printed p. 55, for the cubical/disk pair identification and flattening of the sides. The PDF is not archived in `literature/`; I read the online source at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf and expanded the geometric construction in the proof steps. No SGA source is used.

## What was checked and changed

The target was not already declared in either `WeilConjectures/` source checkout, and no DAG or current blueprint node states this pair homeomorphism. The imported statement was retained exactly, including the n=0 convention, the subspace topology qualification, and the fact that the homeomorphism need only carry the specified subspace setwise. The four Mathlib searches run for the item (LeanFinder, Loogle, grep, and LeanSearch) returned only coordinate-splitting and simplex/cube boundary facts; none states the required pair homeomorphism.

## Review by Q63

I read Hovey Lemma 2.4.13, especially the displayed cubical map and the sentence that it is homeomorphic to the disk-cylinder map by flattening the sides (printed p. 55). I also read the existing `def-kun-subspace-topology` node and quoted its statement in `citations.json`. Step 1 checks the n=0 edge case directly and uses only the induced-topology definition. Step 2 checks the radial cube-to-disk map and its explicit inverse, then the affine rescaling to I^n; the formulas work at the origin by the stated 0 branches. Step 3 spells out the finite PL collar construction: a triangulated collar rectangle maps its lower edge to the lower-plus-right L, product simplices are sent affinely, and the inverse is assembled from the inverse affine pieces. The pieces agree on faces, so the result is a homeomorphism carrying exactly the bottom disk to bottom plus sides; conjugation gives h_n. I tested n=0 separately and n=1, where the target is the three-edge L in the square. No duplicate node was found by searching the DAG and both blueprint snapshots. No new statement was introduced, so there are no new-node searches or duplicate pairs to report. The only nontrivial geometric source is the requested Hovey flattening argument; its details are written directly in Step 3 because no local archive is available.


## Second reading by Q63

- Item statement: compared every hypothesis and both subspaces with Hovey, *Model Categories*, Lemma 2.4.13 proof, printed p. 55, read online at the cited PDF; verdict: correct, with the ambient cube identified on both sides and no pointwise fixing asserted. The source explicitly permits all dimensions, and the stated empty boundary convention handles zero. No Stacks tag applies to this geometric result.
- Original step 1: checked against the statement of `def-kun-subspace-topology` and the empty-coordinate definition; verdict: correct and retained verbatim.
- Original step 2: checked the two radial formulas by taking both norms and composing, including the origin; verdict: correct but unnecessary for an explicit cubical construction, replaced below.
- Original step 3: checked against Hovey's side-flattening sentence; verdict: incomplete under C2/D5/E5, because no collar triangulation or vertex map was specified and the asserted agreement with the identity on the remaining collar was unjustified; replaced by the explicit construction below.
- Repaired step 1: checked `J_0` and the identity of the interval against `def-kun-subspace-topology`; verdict: elementary, correct, and unchanged.
- Repaired step 2: checked both five-triangle lists and their vertex correspondence against the square and Hovey's requested side-flattening; verdict: each fan covers the square, each affine triangle map is invertible, and the common-edge endpoint check plus the finite closed-preimage argument proves continuity in both directions. No triangulation theorem is used.
- Repaired step 3: checked the left edge and both bottom-edge formulas from the vertex values in step 2; verdict: elementary, including positivity of the first coordinate away from the fixed left edge by injectivity of each inverse map.
- Repaired step 4: checked the exact max-radius of each spatial image and computed both inverse composites using `G F = id` and `F G = id`; verdict: elementary, with positive denominators for nonzero spatial inputs and separate axis branches.
- Repaired step 5: checked continuity on the axes, where division is unavailable, from continuity of both square maps and the bound of every output coordinate by its output radius; verdict: correct for every positive finite dimension and for interval endpoints as relative limits.
- Repaired step 6: checked both image inclusions and surjectivity using the explicit preimages `(y/2,0)` and `(((v+1)/2)y,0)`; checked `r(a(u))=1` against the definition of the cube boundary; checked restricted continuity using exactly the open-intersection statement of `def-kun-subspace-topology`; verdict: proves the full setwise pair assertion with the required subspace topologies.
- New nodes: none; B1–B7 introduce no further obligations and no clause of the item is relocated into another node. Searched the DAG and both blueprint snapshots for open-box, pair-homeomorphism and side-flattening language, and opened `lem-coef-topological-serre-model`, `lem-coef-realization-finite-limits` and the parent `lem-coef-serre-homotopy-exact-sequence`; verdict: none supplies this assertion as its statement. Neither read-only Lean source checkout has a matching cubical/open-box declaration.
- Edge cases: `n=0` is the identity; `n=1` gives a square whose bottom is sent onto the bottom and both vertical sides by the two signed spatial rays; the formulas agree at radius `1/2`, at the axis and at every rim. Field/zero-object/empty-scheme cases do not apply to this statement about real cubes.
- Independent Mathlib searches: ran LeanFinder with “A homeomorphism of a closed cube sends one face onto the union of all faces except the opposite face, by a radial extension of a piecewise affine square map” (8 hits, chiefly `Cube.insertAt`, `Cube.splitAt`, boundary and box-face maps); Loogle `Homeomorph, Set.Icc` (9 hits, affine interval and simplex/interval maps); grep `(Homeomorph.*(face|horn|box)|((face|horn|box).*[Hh]omeomorph)|[Pp]iecewise[Aa]ffine)` (1 hit, an implicit-function open partial homeomorphism). Verdict: no matching declaration. Actual search records were appended by `msearch.py` to `searches.jsonl` and recorded in the node.

Changes: replaced the incomplete disk-collar argument with an explicit five-triangle square homeomorphism, its radial cube extension, its inverse, the axis continuity estimates, and exact image preimages; updated `split_report` and agent proof provenance accordingly. Updated `citations.json` for repaired steps 1 and 6 with the verbatim statement excerpt of the sole cited node. The item statement, source, metadata and original worker report/review were retained.

Existing dependency source note (outside this delivery's edit scope): the statement of `def-kun-subspace-topology` supplies exactly the notion used. Its source metadata names `definition-Krull`, item (4), but that item concerns local Krull dimension, not the subspace topology definition. The actual induced-topology convention appears in `literature/stacks-project/topology.tex`, label `item-induced-topology`, lines 74–75. This metadata issue does not change the quoted definition or this proof.
