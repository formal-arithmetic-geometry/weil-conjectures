## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-proj-degree-one-quotients.json` (statement; split; no Mathlib match), `citations.json`, and this report. `searches.jsonl` is the search command's own log. `prepare.py` is a sandbox-only preparation script, not a delivery file.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. The existing general scheme fraction-chart atlas, scheme chart-pullback comparison, and algebraic-space morphism descent statements suffice. The proof has seven steps, none longer than 2000 characters.

## Attachments

None. Searches for the item's exact blueprint tag and for algebraic-space/relative-Proj/line-quotient notions under `lean/WeilConjectures/` found no project declaration with the item's full statement. I read `AlgebraicGeometry/RelativeProj/Universal.lean` and the construction interface in `RelativeProj/Basic.lean`: these characterize or construct scheme relative Proj by affine charts, not the asserted map for algebraic-space source and base. Accordingly this is not an ATTACH claim. The node has no `lean_audit` indicating an upstream open declaration to extract.

## Literature and searches

WANTED: none.

Read the local Stacks sources `spaces-divisors.tex`, Tag 085D, `lemma-relative-proj-generated-in-degree-1`, especially (1) and its omitted proof referring to the scheme case; Tag 0D2Z, `lemma-invertible-map-into-relative-proj`, especially (3) and its scheme-test construction hints; and `constructions.tex`, Tags 01NK and 01O9, both `lemma-invertible-map-into-proj` and `lemma-invertible-map-into-relative-proj`. The 01NK proof constructs the degree-zero ring map by sending an inverse homogeneous generator to its inverse coefficient, and uses uniqueness to glue; that is the fraction normalization supplied by the existing chart-atlas node. Also read `constructions.tex`, Tag 01O4 (`lemma-apply-relative`), the scheme version cited by 085D. Verified the 085D and 0D2Z tag/label pairs in `tags/tags`.

For descent I read `spaces.tex`, Tag 02WU (`lemma-finding-opens`), and `spaces-properties.tex`, Tag 03BZ (`lemma-open-subspaces`), including the invariant-open presentation argument. In our application the invariant open is the whole atlas; the existing descent node explicitly also supplies morphism descent and detection of equality, so I do not use an open-subspace theorem as if it alone supplied morphism descent.

Before considering a new node I searched the whole DAG for 085D, 0D2Z, `lemma-invertible-map-into-relative-proj`, degree-one quotient and fraction-map concepts. This found the existing trace-formula tools, so no new nodes were necessary. `tools/blueprint_refs.py search` was run for `relative Proj`, `invertible.*[Pp]roj|[Pp]roj.*invertible`, `Proj`, `homogeneous fraction`, 085D and 0D2Z. The broad Proj search includes scheme relative-Proj and blowup nodes, and the homogeneous-fraction hit is the Rees fraction-to-chart definition, not this statement. No imported blueprint node states this algebraic-space quotient construction. `ancestor` returns None for the item's already inherited auxiliary chain; its existing `blueprint.from.node = null` and exact supporting route are retained. Read the newest unit text in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` (latest points to main-20261024), together with the DAG chapter and unit records. This is an auxiliary step below the inherited Chow-modification/blowup route, not a change to the unit or chapter.

Ran the prescribed msearch command for the item: LeanFinder and LeanSearch with two concept phrasings, Loogle `"Proj", "invertible"`, and grep `AlgebraicSpace|relativeProj|invertible.*[Pp]roj|[Pp]roj.*invertible` in `AlgebraicGeometry`. The queries and exact returned summaries are appended to the existing `mathlib_searches`, retaining its earlier searches. All services responded. Read `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`, lines 409–450: `Proj.fromOfGlobalSections` (line 443) assumes a scalar ring homomorphism into functions on a scheme and irrelevant-ideal generation. This is useful local machinery but does not specialize in one line to a line-module quotient over an algebraic-space base. The homogeneous localization and affine-chart hits also do not provide the required descent. Loogle's `Module.Invertible.instProjective` is module projectivity, not a Proj universal property. No Mathlib match is claimed.

## What was wrong or changed

The item's statement is unchanged and I found no false hypothesis or clause. Its empty proof did not yet explain why degree-one surjectivity supplies enough charts or why scheme maps over two different base charts agree as maps to the space Proj. The new proof supplies both arguments. The apparent temptation to cite `lem-trf-space-line-module-proj-map` directly would be invalid: that statement has a scheme base T, while this item's base X is an algebraic space. I instead use the smaller existing scheme atlas and comparison statements and write the overlap/descent argument here. The relative-Proj scheme-test node supplies the algebraic-space target and compatible identifications; it is not cited for the line-quotient map itself.

The generic tools belonging to other units are declared with individual reasons in `split_report.tool_uses`. They perform scheme chart construction, module comparison, and descent beneath the inherited geometric route; they do not replace it. No maintainer `tool_uses` field is set.

## Not duplicates

No new nodes were created. Existing nodes are reused rather than duplicated. In particular `lem-trf-line-quotient-homogeneous-fraction-map` is for symmetric algebras on schemes, whereas the smaller general `lem-trf-line-proj-affine-chart-atlas` already applies to our scheme restrictions without introducing a symmetric-algebra detour.

## Review by Q29

I checked the item against 085D(1): its source/base spaces and line quotient are the stated data; A_0 = O_X is an allowed specialization, and degree-one generation is retained even though existence of the map needs only the generating quotient. The fraction normalization follows the actual inverse-generator construction in 01NK and its relative localization in 01O9, as required by 0D2Z(3). I added no finiteness or separation hypothesis and did not assert the extra theta or representability clauses of those source lemmas.

Step 1 uses `def-trf-algebraic-space` for representable diagonals and a scheme etale presentation, `lem-trf-space-fibre-products-etale-covers` for the base-changed etale cover and space fibre product, and `lem-sfb-space-relative-proj-scheme-tests` for the scheme comparison and the target P. I opened each of their statements. In particular T is chosen as an atlas of Y times_X V; I do not incorrectly assume Y times_X V is itself a scheme. T times_Y T and V times_X V are schemes because their two factors are schemes and the respective diagonals are representable. Neither overlap is taken to be affine.

Step 2 uses the stated Zariski--etale equivalence, including its line-module and scheme-pullback comparison, the tensor-normalized composition comparison in `def-sfb-space-module-tensor-composition`, and the ringed-topos tensor comparison. Each statement was read. Only restriction along etale charts is used to preserve surjectivity here; there is no unsupported claim that f is flat or that an arbitrary inverse image is exact. Preservation of epimorphisms under the additive equivalence follows by its universal-property preservation of cokernels. The tensor comparison is applied to the given small sites in the fixed size convention, not to an uncontrolled large index category.

Step 3 uses exactly the affine section isomorphism stated by `lem-weil-pbc-module-pullback-affine-sections`. The rest is the written elementary local-ring argument: a finite linear combination equal to 1 has a unit coefficient at each local stalk. This proves the degree-one cover without treating sheaf-surjectivity as global-section surjectivity on a nonaffine scheme. On each affine W the quasi-coherent source is the displayed tensor module; no finite generation of A_1 is used.

Step 4 uses the statement, not the proof, of `lem-trf-line-proj-affine-chart-atlas`. It explicitly supplies each map, its homogeneous fraction formula and agreement on intersections across affine base opens. `lem-weil-pbc-scheme-morphism-gluing` explicitly supplies existence and uniqueness on this open cover. The scheme-test comparison identifies the resulting target with V times_X P. This step constructs maps; it does not appeal to a new node restating the item.

Step 5 uses precisely the conclusion c composed with q' equals q composed with h from `lem-trf-line-proj-chart-pullback`. I verified that this theorem allows a noncartesian commutative square, arbitrary quasi-coherent graded algebra, arbitrary scheme maps and an invertible module. The input q and q_2 meet its fraction-chart hypotheses by step 4; their data agree by the composition comparison in step 2. The scheme-test statement explicitly gives compatibility with further scheme base change. This proves both maps R to P equal by factoring them through the single Proj over V times_X V. There is no unstated descent compatibility hidden in the word “canonical”.

Step 6 applies the full statement of `lem-trf-etale-open-chart-morphism-descent`, with source Y, atlas T, target P, and O=T. The required relation was proved in step 5. The statement provides the descended map and detection of equality after pullback. For p composed with r equals f I use this detection with target X; I do not apply its scheme-base-only final clause to the algebraic-space base X.

Step 7 reuses the fibre-product etale-cover, chart-pullback, scheme gluing, and etale equality-detection statements just described. A common refinement compares two choices using the same argument as step 5, which applies to any such comparison square. The unit cancellation under a new frame is written explicitly: degree-n coefficients acquire u^(-n), cancelling the nth power of u^(-1) in the denominator. Every step's citations have verbatim supporting quotes in citations.json. I also checked that the atlas, comparison, descent and scheme-test nodes have no dependency path back to this item.

Small cases checked: for empty Y there is only the empty-domain map, so neither the atlas argument nor gluing presupposes a point. If A has no positive degrees, the surjection from A_1=0 onto a line module forces Y empty. For A=O_X[t] and a nonempty source, a degree-one generating image trivializes the pulled-back line, and the construction is the structure map to the relative Proj X. For a nilpotent degree-one generator, a nonempty generator locus is impossible: its image cannot be an invertible coefficient while satisfying nilpotence. Thus the argument does not discard nonreduced algebras or impose reducedness. Infinite-rank A_1 uses all its degree-one sections locally; no finite collection is chosen globally. A nontrivial line is covered by frames, and the explicit cancellation checks their overlaps.

No repairs to the statement, sources, or existing nodes were necessary. The main correction during self-review was to ensure the descent equation is established over the scheme V times_X V, rather than assume the two maps to relative Proj over V have a common base map. All non-elementary facts used here are covered by the existing cited statements. No new unsplit node contains a concealed proof, because there are no new nodes.

## Unfinished work

None in the stage-1 split. No Lean code was written and no compiler, Lake or build command was run. Server dry-run and final push are the remaining delivery operations.
