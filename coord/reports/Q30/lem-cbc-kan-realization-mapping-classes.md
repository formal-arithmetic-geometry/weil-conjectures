# Stage-1 report: lem-cbc-kan-realization-mapping-classes

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-kan-realization-mapping-classes.json`: item, statement unchanged, five proof steps, status split; five freshly logged Mathlib searches, no exact match.
- `dag/nodes/sec-smooth-purity/lem-cbc-realization-singular-unit-weak.json`: new statement-only lemma, unsplit, no Mathlib match after LeanFinder, Loogle, grep, LeanSearch and a second semantic phrasing. States the unit theorem for every simplicial set, independently of the mapping-class comparison.
- `dag/nodes/sec-smooth-purity/lem-cbc-kan-whitehead-inverse.json`: new statement-only lemma, unsplit, no Mathlib match after the same five kinds/phrasing checks. States the converse Whitehead theorem for maps between Kan complexes, with explicit cylinder homotopies.
- `citations.json`: complete verbatim cited statements, one entry for each step/node pair.
- `report.md`: this report. The search wrapper also wrote its actual `searches.jsonl` log. No Lean, source checkout, shared repository, unit record or launcher file was changed.

Two new nodes, zero Mathlib leaves. The existing realization adjunction/horn-pair theorem and cylinder theorem were reused rather than duplicated.

## Attachments

None. The project source was searched for the exact node id, Kan/realization mapping classes, singular complexes, `toSSet`, `sSetTopAdj`, and homotopy equivalences involving Kan complexes. No declaration giving this item was found. The item has no attached Lean declaration to inspect, and upstream-master sorry declarations are not used as proof evidence.

## WANTED

WANTED: archived Kerodon Proposition 3.6.5.2 (0149), Construction 3.6.5.1 (0148), and Example 3.6.2.5 (013H), for lem-cbc-kan-realization-mapping-classes.

WANTED: archived Kerodon Theorem 3.6.4.1 (Milnor, 0142) and Corollary 3.6.4.3 (03X7), for lem-cbc-realization-singular-unit-weak.

WANTED: archived Kerodon Proposition 3.1.7.13 (00UB), converse, and Corollary 3.6.4.3 (03X7), for lem-cbc-kan-whitehead-inverse.

These sources were read online, not downloaded into the project. They are Kerodon tags, not Stacks tags. The Stacks simplicial chapter was searched and its trivial-Kan-homotopy section read; its available theorem concerns trivial Kan fibrations, not these two assertions. Stacks tags 00UB, 0142 and 03X7 have unrelated meanings, so they are not represented here as Stacks citations. No SGA source is used. Because the needed proof document is not archived in literature/, proof_origin.by is agent, and the expanded argument is in the item.

## Problems and corrections

The imported statement is correct with the specified ordinary interval product; it was preserved exactly, including both naturality clauses and empty cases. There is no STATEMENT-DISPUTED finding.

The original item had no proof. Its source referred to a theorem about entire mapping complexes; simply moving that theorem into a child would not split the item. Instead the proof reconstructs the comparison on vertices and edges from the adjunction and cylinder, and obtains the first bijection by explicitly postcomposing with a homotopy inverse to the unit. Neither new lemma mentions mapping classes into an arbitrary Kan target, so neither is a clause of the item in disguise.

A tempting reuse of lem-cbc-kan-mapping-homotopy-invariance is circular: that node cites lem-cbc-realization-weak-equivalence, which cites this item. The existing Kan-Quillen node and the existing Kan-fibration/fiber criterion also reach this item. None is used. The two reused topology nodes were checked transitively and do not reach this item. A future split of the new lemmas must likewise avoid those circular routes: the new nodes assert independent foundational realization/unit and Kan Whitehead facts, not permission to use this item's ancestor as a proof.

Mathlib has the realization/singular adjunction but does not establish the homotopical comparison needed here. I read SingularSet.lean:14–119, including its TODOs at 34–37, and CategoryWithFibrations.lean:66–89. I also read the abstract RightHomotopyClass.whitehead and LeftHomotopyClass.whitehead at ModelCategory/Homotopy.lean:216–236. They require a model-category structure and abstract homotopy relations. Neither the missing realization interpretation of weak equivalences nor the cylinder identification follows merely by specializing them; therefore the new Kan Whitehead lemma is not mislabeled as a Mathlib leaf. All 15 recorded searches actually ran through msearch.py, and their results/digests are copied from its log without invented queries.

The chapter and unit records, their three-level constraints, the current main-20261015 blueprint proof of thm-cbc-finite-level-proetale, and the inherited technical compactification-choice ancestry were read. No unit step is replaced, and this technical item is not the unit's key statement, so no unit realization record is changed. The two cross-unit citations are explicitly declared generic tool uses in split_report.tool_uses.

## Not duplicates

lem-cbc-kan-whitehead-inverse vs lem-cbc-simplicial-homotopy-equivalence-weak: the existing node is the forward implication from a specified simplicial homotopy inverse to a realization weak equivalence, without Kan hypotheses; the new node is the converse for Kan source and target. It cannot be obtained by applying the forward implication.

lem-cbc-kan-whitehead-inverse vs lem-cbc-realization-weak-equivalence: the existing node characterizes realized weak equivalences by testing mapping classes into every Kan target and depends on this item; the new node supplies an actual inverse with cylinder homotopies between two Kan complexes and is not cited from that characterization.

lem-cbc-kan-whitehead-inverse vs lem-cbc-kan-mapping-homotopy-invariance: the existing node concerns precomposition on mapping complexes for an arbitrary weak-equivalence shape and reaches this item; the new node has no mapping-complex conclusion and supplies an inverse for a map of Kan complexes.

lem-cbc-kan-whitehead-inverse vs lem-coef-subdivision-last-vertex-equivalence: the existing node concerns the specific last-vertex map from subdivision, without Kan hypotheses; the new node concerns inverse homotopies for any map of Kan complexes.

lem-cbc-kan-whitehead-inverse vs lem-weil-pbc-etale-ring-map-prescribed-residue-field: only the four-character tag spelling collides; the existing source uses Stacks 00UB for standard etale rings, while the new source is Kerodon 00UB on Kan homotopy equivalences.

lem-cbc-kan-whitehead-inverse vs lem-weil-pbc-standard-etale-monic-derivative: existing statement is about monic derivative presentations of standard etale rings (Stacks 00UB), not simplicial homotopy inverses (Kerodon 00UB).

lem-cbc-kan-whitehead-inverse vs lem-weil-pbc-etale-locally-standard: existing statement is the local standard-etale structure theorem (Stacks 00UB/00UE); the new one is Kan Whitehead (Kerodon 00UB).

lem-cbc-kan-whitehead-inverse vs lem-weil-pbc-standard-etale-pair-maps: existing statement is a polynomial/localization universal-property assertion for standard etale pairs (Stacks 00UB); the new one is Kan Whitehead (Kerodon 00UB).

lem-cbc-realization-singular-unit-weak vs lem-cbc-realization-weak-equivalence: existing statement is a mapping-class testing characterization and depends on this item; new statement is about the explicitly constructed characteristic-map unit for every simplicial set.

lem-cbc-realization-singular-unit-weak vs lem-cbc-kan-mapping-homotopy-invariance: existing statement is about precomposition on internal mapping complexes; new statement is a realized homotopy-group assertion about the unit, before taking any maps out of K.

lem-cbc-realization-singular-unit-weak vs lem-coef-subdivision-last-vertex-equivalence: existing statement concerns a subdivision last-vertex map, whereas the new one concerns X to Sing(|X|); the shared Kerodon 03X7 reference only reconciles weak-equivalence conventions.

The two new nodes also differ from lem-coef-realization-finite-limits: that node constructs the singular adjunction and gives geometric simplex-pair assertions, but says neither that its unit is a weak equivalence nor that a Kan weak equivalence has an inverse. lem-weil-pbc-trivial-kan-homotopy-equivalence requires boundary lifting, which is not the hypothesis of the new Kan Whitehead lemma. Full-DAG keyword/tag/statement searches and blueprint_refs searches for singular, realization, unit map, Kan, Whitehead and homotopy equivalence found no blueprint node stating either new fact. same_as is therefore empty for all three submitted nodes.

## Review by Q30

I read the item against Kerodon 0149 and 0148, then read the actual unit theorem 0142, the Kan converse 00UB, and the convention comparison 03X7. I read 013H for the realization–singular adjunction on the mapping object. This matters because 0149 is a theorem of entire mapping complexes, whereas the item needs just vertices modulo edges and ordinary continuous homotopies; the split proves the passage between those two equivalence relations rather than hiding it in a new node.

For step 1 I opened lem-coef-realization-finite-limits and checked all three clauses used: realizations are k-spaces, realization is left adjoint to the explicitly described singular complex, and every realized horn inclusion is the displayed bottom-face pair. The latter gives a literal retraction by projecting to height zero. Adjunction turns a horn map into a continuous map, and composing with the retraction gives a filler. This small argument is an elementary step, not a new singular-fibrancy lemma. The indices n >= 1 and both outer horns are included, with no unintended zero-dimensional filler requirement.

For step 2 I checked the complete statements of both new nodes: the unit theorem gives the realized weak equivalence for X = W, exactly the hypothesis used in the Kan Whitehead node. W is Kan by the item, and Sing(|W|) was proved Kan in step 1. The inverse and both actual cylinder homotopies are precisely what the second node states. No source-shape Kan assumption or connectedness is inserted.

For step 3 I opened def-cbc-enhanced-diagrams-cones. Its actual internal Fun definition identifies edges with maps K times Delta^1 to the target, and its products are degreewise. Postcomposition respects these edges, and precomposing each chosen inverse homotopy with a times the identity yields exactly the two inverse class equations. This is a direct calculation from the cited definitions and step 2, not an uncited mapping-invariance theorem.

For step 4 I again checked the statement of lem-coef-realization-finite-limits for the actual-map adjunction, and opened lem-coef-simplicial-realization-cylinder for the displayed homeomorphism and its endpoint formulas. These match K times Delta^1 and the ordinary product |K| times [0,1], not only a k-ified arbitrary product. The adjoint maps and inverse formulas are written out. Applying them to a homotopy works in both directions. Reversal and finite concatenation of continuous homotopies prove that the edge-generated equivalence closure is exactly the continuous-homotopy relation. No claim about a non-locally-compact arbitrary product is needed.

For step 5 I substituted the formula for the characteristic-map unit into the adjunction formula and obtained |a| exactly. For precomposition r and postcomposition s I compared the two pointwise quotient formulas, which coincide. Composing actual homotopies proves both operations descend to classes. I tested K empty, W empty with K nonempty, both empty, discrete Kan targets and the point. The unit theorem has the empty-to-empty identity in its empty case; for Kan Whitehead an empty source and the component bijection force an empty target. The explicit homotopies therefore introduce no hidden nonemptiness assumption. Both new statements are self-contained, have only definition dependencies, and carry no proof or hidden proof sketch.

I checked delivery-errors B through E individually against the submitted files: self-contained objects and definitions, single-escaped TeX, correct source identifiers, actual search logging, explicit blueprint ancestry, no available attachment, every non-elementary input cited by statement, no use of another node's proof, no cycle through the existing invariance/Quillen package, generic tool-use declarations, no moved clause, all hypotheses checked, and the actual comparison/naturality formulas expanded. The only corrections needed during drafting were to avoid circular existing packages and to use the ordinary cylinder theorem explicitly instead of claiming realization preserves arbitrary ordinary products. citations.json contains the complete statement of every cited node so the second reader can test every claim directly.

## Remaining work

The intended one-level split is complete. Both new foundational lemmas remain unsplit as required. No delivery push is authorized for this worker; the sandbox is handed to a fresh second reader after the required successful dry run. Server-check and final dry-run results are recorded below as they complete.

## Second reading by Q30

- Step 1 checked against Kerodon Proposition 3.6.5.2 (0149) and the cited realization/horn statement; the retraction argument proves singular fibrancy for all horns, including outer horns, and is elementary under the cited node.
- Step 2 checked against Kerodon Theorem 3.6.4.1 (0142) and Proposition 3.1.7.13 (00UB); both Kan hypotheses and the realization weak-equivalence hypothesis are present, and the cited Whitehead statement supplies the displayed inverse and cylinder homotopies, including empty cases.
- Step 3 checked against the complete definition of the internal functor in def-cbc-enhanced-diagrams-cones and the endpoint equations in the Whitehead node; postcomposition preserves edge-generated equivalence and the two cylinder homotopies give inverse maps on classes.
- Step 4 checked against Kerodon Example 3.6.2.5 (013H), Construction 3.6.5.1 (0148), lem-coef-realization-finite-limits, and lem-coef-simplicial-realization-cylinder; the adjunction and ordinary product cylinder identify edges exactly with continuous homotopies, with the equivalence-closure argument written out.
- Step 5 checked against Construction 3.6.5.1 (0148) and the item statement; the characteristic-map formula is exactly realization, both naturality clauses are pointwise correct, and empty source/target cases satisfy the same bijection.
- New node lem-cbc-realization-singular-unit-weak checked against Kerodon Theorem 3.6.4.1 (0142), clause by clause; its singular construction, weak-equivalence conclusion, and absence of extra hypotheses agree. Its Mathlib searches were run and record no exact declaration.
- New node lem-cbc-kan-whitehead-inverse checked against Kerodon Proposition 3.1.7.13 (00UB), clause by clause; “homotopy” is represented by the stated simplicial cylinders, and no connectedness or nonemptiness is added. Its Mathlib searches were run and record no exact declaration.
- The item statement was checked against Kerodon Proposition 3.6.5.2 (0149), Construction 3.6.5.1 (0148), and Example 3.6.2.5 (013H); its component-level formulation and ordinary topological homotopy quotient are the required consequence.
- I searched the full DAG for realization/singular-unit, Kan Whitehead, and mapping-class variants; no existing node duplicates either new lemma. The cited nodes were opened and their statements, rather than their proofs, support each step. The dry-run delivery preflight passed at commit 8fa773600e.

Changes made during second reading: none to the mathematical statements or proof steps; appended this hypothesis-by-hypothesis review and recorded the successful dry run.
