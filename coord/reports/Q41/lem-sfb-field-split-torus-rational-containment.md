# Q41 stage-1 report: lem-sfb-field-split-torus-rational-containment

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-split-torus-rational-containment.json: item, statement, split into five steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-split-torus-flat-quotient.json: new statement-only unsplit node, no Mathlib match. A faithfully flat quotient of a split torus is split over the original arbitrary field.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-maximal-split-tori-conjugacy.json: new statement-only unsplit node, no Mathlib match. Rational conjugacy of two maximal split tori in a connected reductive group over an arbitrary field.
- citations.json: one verbatim statement quotation for each of the eleven step/node citations.
- searches.jsonl: actual msearch.py results; the node records retain the exact tool and query. prepare.py is a sandbox-only JSON preparation script.

## Attachments

None. Searching lean/WeilConjectures/ for the item id, maximal split tori, split torus/tori, diagonalizability, and group homomorphism factorization found no declaration asserting this item or either new input. The split-torsor hits are unrelated sheaf constructions.

## WANTED

None. Milne's iAG2017 PDF is available locally and was read with pdftotext. No source was downloaded and no SGA source is used.

## Findings and corrections

The item was unsplit and there was no earlier sandbox proof, report, citations file or search log to continue. I preserved its statement, statement dependencies, created metadata and inherited blueprint ancestry. No repair note was present. Its source is Milne, not a Stacks theorem, so the new sources name the exact theorem numbers and printed pages rather than inventing Stacks tags. The blueprint latest symlink points to main-20261024; I read its six-functors-basics stability unit and direct-images proof. The inherited ancestry describes the residue-field input in the DVR-torus argument. This delivery supplies only that field input, with no alteration of the chapter or unit route, no DVR lifting assertion, and no realization edits to a unit whose key node this is not.

The algebraically closed hypotheses of the existing torus-image and maximal-torus conjugacy nodes cannot be dropped. In particular geometric conjugacy alone cannot yield the required element of G(k). I explicitly use a new arbitrary-field split-quotient statement and a new rational maximal-split conjugacy statement. I also retain the faithfully flat image, instead of treating its B-points as the ordinary image of D(B): such surjectivity would fail for power maps over many B.

The item has blueprint.from.node = null in the live repository and the ancestor command prints None. I retained that inherited anchor and followed the required via list for new children. The exact supporting places and same_as=[] are filled. Whole imported-blueprint searches for 'split tor', 'split torus', 'maximal split', '12.14', and 'quotient torus' found no statement duplicate. A 'conjugacy' search found arithmetic/Frobenius and trace-related statements, not algebraic-group split-torus conjugacy. I also searched the latest blueprint text for the torus assertions.

## Not duplicates

lem-sfb-field-split-torus-flat-quotient vs lem-sfb-torus-homomorphism-image: the existing statement requires an algebraically closed field; the new statement asserts splitness over any original field for a faithfully flat quotient.

lem-sfb-field-split-torus-flat-quotient vs lem-sfb-diagonalizable-quotient-character-kernel: the existing statement assumes an algebraically closed field and identifies a diagonalizable cokernel; it does not give the arbitrary-field split-torus quotient statement.

lem-sfb-field-split-torus-flat-quotient vs lem-sfb-split-torus-subgroups-diagonalizable: that statement classifies closed subgroups over an algebraically closed field; this one concerns quotients and makes no closure assumption on the field.

lem-sfb-field-maximal-split-tori-conjugacy vs lem-sfb-cocharacter-conjugate-maximal-torus: the existing result concerns a rank-one source over an algebraically closed field, not rational conjugacy of maximal split subgroup schemes over arbitrary fields.

lem-sfb-field-maximal-split-tori-conjugacy vs lem-sfb-borel-maximal-torus-conjugacy: the existing theorem assumes an algebraically closed field and concerns Borel subgroups and maximal tori; the new theorem concerns maximal k-split tori and a conjugator in G(k).

Neither new statement restates the item: the quotient lemma makes no reference to a reductive ambient group or conjugation, and the conjugacy lemma has two maximal subgroup schemes as inputs, no general homomorphism, no kernel and no nonmaximal image. The item's image construction, maximal extension, and morphism factorization remain written out in its proof.

## Review by Q41

I read Milne Theorem 3.34 on printed p.75, Theorem 12.9(b),(c) and its proof on pp.233--234, Definition 12.14 and the following quotient paragraph on p.236, and Theorem 25.10 with its section's reductivity assumption on pp.544--546. I also read Theorem 5.39, Remark 5.42 and the quotient-map criterion on pp.108--109 to check that faithfully flat quotients, not rational-point surjections, are intended. For the new quotient node, the sentence following Definition 12.14 states exactly that a quotient of a split torus is again split; Theorem 12.9 explains why this holds over k, not merely over its algebraic closure. For the new conjugacy node, Theorem 25.10 explicitly gives an element of G(k), and the section assumes G reductive over the arbitrary field k. These are real theorem inputs, not elementary facts hidden as definitions.

For step 1 I opened both existing coordinate and affine-image statements. The coordinate node gives the split presentation, affineness and finite type without its separate monoscheme hypothesis. The affine-image statement allows arbitrary fields and supplies an affine finite-type I, a closed embedding j, and a faithfully flat u with f=ju. This meets exactly the hypotheses of the new quotient node; I did not apply the algebraically closed torus-image theorem. The coordinate finite-type assertion and the image/quotient assertions are quoted in citations.json.

For step 2 I read the full statements of lem-kun-dimension-finite-type, lem-trf-lattice-torus-coordinates-action, lem-trf-split-lattice-torus-projection and def-kun-dimension. They give, respectively, finite dimension of this finite-type G, the coordinate algebra for every split R, the domain property of that algebra over k, and the strict-chain definition. The domain assertion holds for every extension K/k, so K=k is allowed. The argument that the zero prime makes R irreducible and that chains in its closed underlying space remain chains in G is written out. I use no dimension formula for ranks, smoothness descent, or unproved subgroup-containment assertion.

For step 3 I checked the affine quotient-ring clause of def-weil-closed-immersion and the exact chain definition of def-kun-dimension. A nonempty finite set of attained dimensions has a greatest value. A strict subgroup inclusion in a torus cannot have full support because its defining ideal would lie in the zero prime of a domain. Appending the irreducible ambient torus to a longest chain therefore strictly increases dimension. Those short arguments prove maximal containment; they are not new nodes. The ideal factorization explaining that M to R is a closed immersion is included. No Noether-normalization theorem or topological dimension-drop lemma is silently invoked here.

For step 4 the new conjugacy statement says precisely that c_g restricts from the first maximal split torus to the second. Both M and S are maximal k-split subgroup schemes of the same G; G already has all its smoothness, geometric connectedness, reductivity, affineness and finite-type hypotheses. The order S_1=M, S_2=S checks the orientation. For step 5 I read the multiplication, inverse and homomorphism clauses of def-sc-group-scheme. Composition constructs v; the displayed equality follows as an equality of morphisms and can then be evaluated on every algebra. There is no upgrade from equality only on k-points.

I tested the statement and both new nodes on the trivial torus, trivial f, G equal to a split torus, an anisotropic reductive G with S=1, finite k, and imperfect k. For an anisotropic G the image/containment argument forces the split image to be trivial. In characteristic p the map G_m to G_m, t maps to t^p, has nonreduced kernel mu_p but split quotient G_m, so it is intentionally included. No step requires that kernel to be smooth. I did not use a false assertion that all subgroups of a torus are tori (mu_p is the immediate counterexample). The dimension argument uses reducedness of the larger torus only, proved by its domain coordinate algebra.

The new nodes have self-contained objects and inline definitions of split torus, reductivity, unipotence and the rational-point conjugation being asserted. Their non-inline notions cite definition nodes that I opened. They have no proof, proof dependencies or proof sketch in their statements. All searches were run through msearch.py, with a second phrasing for each missing fact. The hits are abstract group quotients/conjugacy, arithmetic subgroups, Lie Cartan statements, formal-smoothness splitting conditions, and affine flatness statements; reading their displayed types rules out an exact match or one-line specialization. The broad quotient grep produced substring hits such as factorization; a second word-boundary grep confined to AlgebraicGeometry produced none. No leaf is claimed. No service failure was reported as absence.

I checked delivery-errors B1--B10 for self-containment, literal TeX, sources, actual searches, lack of a finished Lean match, and blueprint references. For C1--C8 I opened every cited statement, copied the relevant text into citations.json, checked each hypothesis above, and declared the three generic cross-unit statement uses in split_report.tool_uses. I checked their dependency closures and none reaches this item. For D1--D5 the proof retains the image, maximal-containment and assembly arguments rather than moving the item wholesale into a child. For E1--E7 the arbitrary-field and nonreduced-kernel tests above check the real objects and hypotheses; no statement correction is needed. Every proof step is below 2000 characters; none hides a separately hypothesized lemma.

## Source caution

Milne's statement 25.10 is the rational conjugacy theorem needed here. Its short displayed proof says that a nontrivial split torus forces a proper parabolic via 25.2, whereas 25.2 requires a noncentral split torus. For G=G_m there is a nontrivial central split torus and no proper parabolic. This is a gap in that line of the displayed proof, not a counterexample to the theorem or to this item. A later split of the new conjugacy node must explicitly handle the central case before that induction. I do not copy the faulty inference into this item's argument. I also do not rely on the uniqueness wording of 25.6(c).

## Unfinished work

No required stage-1 work is intentionally omitted. The two new unsplit theorem inputs are queued for their own stage-1 splits, as the one-level protocol requires. No Lean source, build or compiler was used or changed; all writes are in this item's sandbox.

## Validation

The required deliver.py --no-push completed with exit 0 and OK at 64455110c46; server preflight passed. The single admitted dry run finished before the push invocation.
