# Q80 — lem-coef-coherent-fixed-vertex-cofibrations

## Files written

- dag/nodes/sec-six-functors/lem-coef-coherent-fixed-vertex-cofibrations.json: statement, split; inherited statement and search history retained, five proof steps added. No Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-coherent-simplex-boundary-cube.json: statement, unsplit; the exact mapping sets and composition of the realized simplex boundary. No Mathlib match. This node has no proof or proof dependencies.
- citations.json: one verbatim statement excerpt for every node cited in the five item steps.
- searches.jsonl: actual searches run by msearch.py, including two phrasings of the structural boundary calculation, and fresh searches for the item. The script's first grep used a single-file target and printed a malformed file field (14); I did not record that defective result in either node. I repeated the relevant grep against the AlgebraicTopology directory and read the source directly.
- report.md: this report.

## Attachments

None. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 by the exact blueprint tag, item id, fixed-vertex/coherent-cofibration terminology, SimplicialThickening, coherentRealization and rigidification found no project declaration stating the item or the new structural lemma. Hits about Artin–Schreier rigidifications are unrelated. No upstream master sorry declaration is treated as finished.

## Literature wanted

WANTED: Jacob Lurie, Higher Topos Theory, Section 1.1.5 and Theorem 2.2.5.1, the initial cofibration calculation on printed p. 90 (PDF p. 107), archival copy for both the item and lem-coef-coherent-simplex-boundary-cube. I read the Harvard-hosted PDF online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf; nothing was downloaded into the project. The item proof is marked agent-written because the local blueprint supplies the ancestry rather than these technical details. No Stacks tag states this enriched simplicial result. No SGA source was used.

## Findings and corrections

The imported item statement is consistent with its source and was not changed. It is narrower than the full Joyal–Bergner theorem, and using that downstream theorem would conceal the calculation and risk a dependency cycle. The proof uses only its initial boundary calculation. The relative simplex decomposition was already in lem-coef-infinity-monomorphism-boundary-cells, so no decomposition node was created. Likewise the Kan-Quillen lifting input was already in the independent lem-coef-kan-quillen-model-right-proper-core; I avoided the broader right-proper node's coherent-localization dependencies.

The item is a technical descendant, not the key statement of its unit. I read sec-six-functors and sk-prop-sf-biduality-general and the current main-20261015 prop-coef-integral-exceptional-adjoint.proof.md. The ancestry serves its second paragraph's derived coefficient adjunction. The generic simplicial calculation does not replace any chapter or unit step; no unit record or maintainer-owned metadata was changed.

## Unfinished work

The one new structural calculation remains statement-only, for its own subsequent split. There is no omitted part of the item's proof beyond that expressly cited dependency. No Mathlib leaves were created. The sandbox is for a second reader; this worker does not push a delivery.

## Not duplicates

lem-coef-coherent-simplex-boundary-cube vs lem-coef-coherent-fixed-vertex-cofibrations: the new lemma computes every mapping set of one finite boundary realization and its composition; it asserts no cofibration or lifting property. The item proves lifting for arbitrary small fixed-vertex inclusions by a dimension filtration and Kan-Quillen lifts.

lem-coef-coherent-simplex-boundary-cube vs lem-coef-pinched-cube-latching: the latter defines coherent realization and computes the collapsed cone's mapping space Q^n and its latching maps. It does not compute the uncollapsed boundary simplex's extreme mapping set.

lem-coef-coherent-simplex-boundary-cube vs lem-coef-coherent-nerve-relative-cube-comparison: the latter assumes a locally Kan target and compares extensions and relative homotopy classes into its coherent nerve. It does not identify the boundary realization as a simplicial subcategory, and its coherent-nerve/rigidification dependencies are downstream of this foundational argument.

lem-coef-coherent-simplex-boundary-cube vs lem-coef-coherent-nerve-comparison: the latter states the whole Bergner–Joyal equivalence and mapping-space comparison, but does not state the finite boundary mapping-set calculation. No use is made of its proof or its Quillen-equivalence assertion.

Whole-DAG keyword searches and whole-blueprint searches for coherent realization, skeletal, boundary cube, coherent boundary, and simplicial cofibration were read before creation. The coherent-realization blueprint matches are coefficient-adjunction or definition contexts, not this structural statement. The new id has no existing occurrence. There is no same-Stacks-tag pair: these are not Stacks results.

## Review by Q80

I read the item and new lemma against the opening paragraph of the proof of HTT Theorem 2.2.5.1, in particular the separate n=0 case and the n>0 extreme mapping cube. The item excludes new vertices, so n=0 contributes no cells. The new lemma uses exactly the n>0 calculation, including the coordinate-zero proper faces and coordinate-one composition faces. This is a genuine structural lemma, not an assertion that a smaller instance of the item's map is a cofibration. I checked that it states its objects, boundary, product cube, empty union convention and composition without referring to a proof sketch or to a tag for its meaning.

For step 1 I opened lem-coef-infinity-monomorphism-boundary-cells: its statement gives the actual sequential relative presentation indexed by missing nondegenerate simplices, not merely a retract of a cell complex. The small indexing sets and absence of missing zero-simplices follow from the item's hypotheses. I also read its source, Kerodon Tag 0077, proof of Proposition 1.5.5.14(b), online. Every stage retains O.

For step 2 I opened lem-coef-pinched-cube-latching: its statement explicitly defines the simplex enriched categories, union composition, their operators, and the simplex-indexed colimit. I use only those definitions, not its pinched-quotient theorem. The proof writes out the universal bijection with compatible simplex functors and the resulting colimit property. Fixing the object function restricts this universal property to sCat_O. It does not assume mapping spaces compute pushouts objectwise.

For step 3 I reread the new node's statement. It supplies all the mapping-set identifications used, including the composition faces; these are quoted in citations.json. The argument then checks the enrichment constraints: only composites through an interior vertex can land in the extreme mapping set, and they lie on its prescribed boundary. New arrows have no composable nonidentity arrows on either side inside the abstract simplex category. Identifying some vertex labels in E or F does not create new composability constraints in that domain.

For step 4 I opened lem-coef-kan-quillen-model-right-proper-core. It states the Kan model structure with precisely monomorphisms as cofibrations and the same horn fibrations and geometric weak equivalences as the item. Thus the cubical boundary inclusion, a degreewise injection, lifts against the given mapping-space trivial fibration by the model axiom. This use requires no Kan hypothesis on either source or target mapping space. The node, not just a definition of trivial fibration, is cited. The coincidence of coordinate faces ensures the previous enrichment check applies to the selected cube lift.

For step 5 the induction starts with the specified top functor and extends its boundary data at every cell. The sets of cells are small, and choice selects a lift for each; the pushout gives a single functor extending the previous stage. The sequential colimit then gives the diagonal, with both triangles verified by restriction to stages. These are universal-property arguments written in the step, not a separately asserted stability theorem.

I checked small cases: n=1 gives two discrete boundary objects and the empty boundary of Q_0, so surjectivity on vertices of the mapping-space trivial fibration is essential and present. At n=2 the extreme mapping set is an interval with two endpoints, the direct edge and the composite. If K=L all cell sets are empty and the diagonal is the given functor. If O is empty both simplicial sets are empty. Arbitrary loops in L and repeated labels are allowed. None of these tests adds hypotheses.

The new searches returned ordinary simplex boundaries, topological cube boundaries, SimplicialThickening/its nerve, and SSet cofibration declarations. I read Mathlib/AlgebraicTopology/SimplicialNerve.lean:12-125,153-224, SimplicialSet/Boundary.lean:30-55 and SimplicialSet/CategoryWithFibrations.lean:35-100. They do not state the enriched boundary realization or the item; the SSet cofibration declaration alone is not an attachment or an enriched-category leaf. Every new recorded query matches an actual msearch.py log entry. I checked delivery-errors B–E against the files: self-contained statement, no hollow data, no disguised clause node, no unquoted citation, no unproved transport, and no unreported statement change. The explicit citation excerpts are verbatim substrings of the node statements.

## Validation

Required command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q80 lem-coef-coherent-fixed-vertex-cofibrations --no-push`. The final one-line handoff reports its outcome; READY is used only after this command prints OK. No local compiler, Lake command, or local DAG/preflight checker was run. No delivery is pushed.

## Second reading by Q80

I reopened the HTT PDF at Theorem 2.2.5.1, printed p. 90 (PDF p. 107), and the local statements of every cited DAG node.

- Item statement: checked each hypothesis against the HTT boundary-cell calculation and the fixed-object mapping-space lifting formulation; the degreewise injection, vertex bijection, object set, trivial Kan-fibration definition, and absence of local Kan hypotheses are all present and no clause was changed. Tested the empty simplicial sets, a field-like one-point mapping set, the empty object set, and n=1.
- New node `lem-coef-coherent-simplex-boundary-cube`: checked the object set, all ordered-pair mapping sets, the characteristic-function cube, the n=1 empty-boundary convention, and both kinds of boundary faces against the explicit HTT calculation. The n=2 case gives the two endpoints of the interval; no Mathlib declaration supplies this enriched calculation.
- Step 1: reread `lem-coef-infinity-monomorphism-boundary-cells` and its Kerodon relative skeletal source. It supplies the sequential pushouts and explains why no 0-cell is attached when the vertex map is bijective; the statement supports the step under the item's hypotheses.
- Step 2: reread `lem-coef-pinched-cube-latching` and `lem-coef-simplicial-interval-lifting`. The simplex-colimit universal property gives the displayed mapping-out bijection and fixed-object restriction; no objectwise mapping-colimit claim is used. This is a direct two-paragraph universal-property argument, so the elementary marking is appropriate.
- Step 3: reread the new boundary-cube statement. It supplies exactly the exceptional mapping set and its composition faces; the remaining compositions are identities or prescribed boundary composites. Repeated vertex labels were checked by keeping the abstract simplex objects distinct and using the prescribed object map into O.
- Step 4: reread `lem-coef-kan-quillen-model-right-proper-core`. Its Kan–Quillen model structure makes every degreewise injection a cofibration and identifies the item's mapping maps as trivial fibrations, including the n=1 map `∅ → Δ⁰`; no fibrancy assumption is smuggled in.
- Step 5: checked the coproduct pushout and sequential-colimit induction against the source filtration. Smallness permits the choices, each extension agrees on its attaching boundary, and both diagonal triangles restrict correctly at every stage. The empty stage and n=1 cases were checked explicitly.
- New-node form: the structural node is statement-only, self-contained, uses its definition dependencies, has TeX once, records the HTT source, and carries the five recorded LeanSearch/LeanFinder/Loogle/grep searches; whole-DAG searches found no duplicate. No Mathlib leaf exists.

No mathematical or citation repair was needed after this reading. I retained the worker's report and search records unchanged; the only addition is this second-reading audit.
