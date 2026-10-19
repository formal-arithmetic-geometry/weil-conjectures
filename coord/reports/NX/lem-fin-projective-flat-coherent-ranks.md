## Files written

- `dag/nodes/sec-smooth-purity/lem-fin-projective-flat-coherent-ranks.json`: existing item split; no new nodes.
- `citations.json`: verbatim statement quotes for every proof-step citation.

## Attachments

None. No sorry-free declaration for this item was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None.

## What was wrong in the node, blueprint, or brief

The imported proof had two paragraphs but left the Noetherian-to-constructible-topology passage implicit and marked the matrix argument's step elementary as null. I expanded it into five explicit steps. I also replaced the unqualified claim that a projective module is free on a “further finite open cover” with the existing finite-principal-cover node, and made the geometric residue-field extension comparison explicit. No statement correction was needed. The existing finite-free-complex upper-semicontinuity node already contains the minors argument, so no duplicate matrix-rank node was created.

## Review by NX

I read the item, its unit and chapter records, the master blueprint proof, and Stacks Project `perfect.tex` at Tags 0BDN and 0BDI (including the proof of the jump-loci lemma). I checked the existing statements of every cited node: the Picard-framework perfectness and arbitrary base-change lemmas, the perfect-complex definition, the finite-projective standard-free-cover lemma, the localized pullback model lemma, the geometric-fibre definition, cohomology definition, the affine finite-free-complex upper-semicontinuity lemma, and the constructible-subset definition. Step 1 verifies the Noetherian topological hypothesis from the supplied affine-cover and quasi-compact definitions. Step 2 checks all hypotheses of the perfectness lemma and refines its finite projective models to finite free ones. Step 3 checks that the base-change target is exactly the geometric fibre and spells out why extending the residue field preserves the finite-dimensional homology dimension. Steps 4 and 5 use the cited finite-free lemma to form finitely many locally closed level sets and then take their finite union over the cover. I tested the edge cases of rank zero, a one-term complex, an empty base, and an algebraically closed residue field (where the extension comparison is identity). I corrected the original missing citations and supplied citations.json with verbatim quotes.

## Second reading by NX

- Item statement: compared all hypotheses and the geometric degree-$r$ conclusion with the master blueprint node (order 1609) and perfect.tex, Tags 0BDN (lemma-jump-loci-geometric) and 0BDI (lemma-jump-loci); the blueprint specializes the source to projective morphisms over Noetherian bases and requests global constructibility. Valid, unchanged. The split directly uses the existing projective perfectness/base-change statements, so it does not silently assume the stronger source hypotheses.
- Step 1: read pqf-def-locnoeth, the quasi-compact definition, lem-sc-affine-noetherian-underlying-space, and the constructible definition. The finite affine cover exists by quasi-compactness; every chart intersection with an open is quasi-compact by Noetherianity. Finite union gives the required Noetherian topology. Valid.
- Step 2: read the projective perfectness statement, perfect-complex definition, and finite-projective standard-free-cover statement; all hypotheses hold. The common refinements are principal opens D(product), so remain affine, and there are finitely many terms and charts. Compared with the first blueprint paragraph and algebra.tex, Tag 00NX, lemma-finite-projective, (3) and (7). Valid.
- Step 3: read arbitrary base-change and localized perfect-model statements, the geometric-fibre and cohomology definitions; base change allows the non-Noetherian geometric target, and the model is strictly perfect. Added the module-pullback and affine-spectrum definitions and wrote the tensor-matrix and exact-global-sections arguments explicitly. The boundary/cycle complements prove preservation of homology dimension by field extension. Valid after repair.
- Step 4: read lem-sc-finite-free-complex-homology-upper-semicontinuous and compared with perfect.tex, Tag 0BDI, final proof paragraph. The difference of successive open sublevel sets is locally closed; the middle-term rank bounds all dimensions. Valid, with no hidden appeal to the cited node's proof.
- Step 5: read the constructible definition and compared with the second blueprint paragraph. Finite unions of the chart level sets are constructible in the Noetherian base and their fibres give the disjoint finite partition; the empty-base case avoids a nonexistent maximum. Valid.
- New nodes: none; no new statements, Mathlib leaves, or B1–B7 forms require review. Existing finite-free semicontinuity and finite-projective free-cover nodes already supply the non-elementary algebra, so no duplicate or clause-restatement nodes were added.
- Edge cases: zero sheaf/zero complex gives the constant zero function; a one-term complex gives its free rank; over a field the base has one point and field extension preserves dimension; r=0 uses the incoming degree -1 differential (zero for connective models); an absent degree gives rank zero; the empty base has the empty partition. No statement dispute.
- Upstream check: searched the item id and cohomology/constructibility vocabulary in the read-only source checkouts and read slopmaster2 DirectImage/Semicontinuity.lean. upperSemicontinuous_hFiber is a related semicontinuity theorem, not the exact global geometric constructibility statement; no exact finished attachment found. Master sorry declarations were not used as proofs.
- Changes: expanded Step 3's ordinary-pullback and cohomology identification and added two definition citations with verbatim quotes. Retained split_report.tool_uses as proposed tools: review_split.py lines 99–100 explicitly permit worker proposals and reserve copying to the maintainer-owned top-level tool_uses field for merge. All first-worker report sections retained. No other steps or the statement were rewritten.

Cross-unit tools requested for maintainer review (split_report proposals only; no maintainer-owned top-level tool_uses field set):

- lem-pc-projective-noetherian-rf-perfect: Perfectness of coherent projective direct image; the item explicitly follows this Picard-framework input and its unit supplies no replacement.
- cor-pc-projective-noetherian-rf-perfect-base-change: Arbitrary geometric-point base change of coherent direct image; the item explicitly uses this Picard-framework input.
- lem-weil-pbc-finite-projective-standard-free-cover: Finite free trivializations of finite projective modules; a general algebra tool for the imported refinement, absent from this unit.
- lem-pc-localized-pullback-perfect-model: Computes derived pullback from a supplied local strictly perfect representative; a generic local-model tool absent from this unit.
- lem-sc-finite-free-complex-homology-upper-semicontinuous: Open sublevel sets for a finite free complex on an affine scheme; implements exactly the imported matrix argument and is more general than coherent fibre cohomology.
