# Q16 stage-1 report: lem-coef-cone-boundary-projective-cells

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cone-boundary-projective-cells.json`: statement, split; no exact Mathlib match. Seven explicit proof steps; the imported statement is unchanged.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `searches.jsonl`: actual searches logged by msearch.py. Inherited item searches are preserved; the seven Q16 searches are appended with their returned declarations and verdicts.

## New nodes

None. The proof uses existing nodes lem-coef-pinched-cube-latching and lem-coef-simplicial-interval-lifting. No Mathlib leaves created.

## Attachments

None. Searching the complete project `WeilConjectures/` tree for the item tag and the notions straightening, coherent cone, pinched cube, and simplicial collage found no declaration for this assertion. The upstream master is reference material only; no sorry declaration is counted as a proof.

## WANTED

WANTED: Jacob Lurie, *Higher Topos Theory*, §§2.2.1–2.2.2, printed pp. 73–76, for lem-coef-cone-boundary-projective-cells. The file is not archived in literature/. I read those pages online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf on 2026-10-17. The proof_origin is agent: the explicit word-quotient calculation expands the source's brief correspondence description and point calculation. No SGA source is used. No Stacks tag states this specific simplicial enriched construction.

## Errors and changes

The current repository statement is already the maintainer-reviewed trimmed version, titled “Free coherent cone modules: collage structure and point formula”. Its older name and some inherited search queries still mention projective cells. I preserved the current statement, including every naturality and size clause, and did not restore the removed cocontinuity, cofibration or homotopy-pushout assertions. The old item had no proof or proof dependencies. It now has the required complete proof. Its historical ancestry and unit metadata are preserved; the current main blueprint ancestor lives in sk-thm-sf-package, and its paragraph 2 is the same derived coefficient-adjunction display served by this technical input.

The main trap in extending the point calculation is the empty simplicial set: an unqualified colimit of cone categories indexed just by its simplices would forget the cone vertex. Step 5 instead fixes both the copy of A and v and gives the compatible-family universal property explicitly. The second trap is assuming mapping sets preserve enriched colimits. Steps 2–6 calculate degreewise word relations and the actual quotient, so no such theorem is assumed.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. I searched all blueprint nodes with blueprint_refs.py for “pinched”, “collage” and “straightening” (all returned zero), and searched DAG statements for those notions and coherent cones. Existing cone-presheaf-adjunction concerns the projective model structure and an adjunction, and depends on the straightening framework; it is not used here. The existing operadic-collage-comparison and infinity-fiber-colimit-collage have different objects and hypotheses. The pinched-cube node is reused for the simplex data and Q, not restated as a child. The current main blueprint ancestor's proof and the item's chapter/unit records were read. No route step is replaced.

## Review by Q16

I read HTT's §§2.2.1 and 2.2.2 online: the first introduces the amalgamated cone correspondence, and the second defines the point construction using the cosimplicial pinches J and Q. For the source route I also read the current main-20261015 prop-coef-integral-exceptional-adjoint proof paragraph 2 and the historical chapter/unit records. There are no new nodes to check against additional sources. I opened the entire statements of both cited nodes: pinched-cube-latching defines the subset-poset realization, its simplex-colimit extension, J, Q and Q^0; simplicial-interval-lifting explicitly asserts completeness and cocompleteness of small simplicial categories. I use only these clauses, never their proofs or model-category claims. The following are the actual step checks, against delivery-errors B–E.

Step 1 uses interval-lifting for existence of the small enriched colimits and pinched-cube-latching for the definition of C on simplices and by simplex colimit. The colimit preservation assertion is proved here by the mapping-out bijection, with the target simplicial set defined explicitly. The indexing category is small: K and X have small simplex sets. No arbitrary-size colimit is introduced.

Step 2 uses pinched-cube-latching's subset-poset mapping sets and union composition. Restriction to the initial face is exactly the old realization. The degreewise word construction is written out, including its relations, simplex operators and mapping-out test. No directed word can return from the cone vertex to an old vertex; relations with old endpoints reduce to those already present in the initial faces. This proves the full-subcategory claim, rather than merely asserting it for a pushout. X empty is checked separately.

Step 3 needs no additional node: it repeats that word calculation for the actual amalgamation with A. The functor aC[p] may collapse vertices and mapping simplices; no faithfulness or monomorphism is needed. All base-only words reduce using the specified functor to A, with no new relation in A. Associativity and the identity in this concrete category give the enriched presheaf action.

Step 4 cites pinched-cube-latching for the actual definition Q^n=C[J^n](x,v). Step 1 gives the pinch pushout, and Step 2 supplies its remaining mapping sets. Attaching it at b=a(s) gives arrows with one final Q-letter, so the inverse to the displayed product is explicitly the composed old prefix together with that letter. All old simplex mapping sets are identities because the base map factors through the one-object identity category. This hypothesis holds precisely for the constant simplex over s; it is not asserted for general simplices of S. Compatibility with monotone maps is the Q action in the cited statement.

Step 5 uses the already established simplex calculation and writes the exact compatibility relations for arbitrary K. The fixed A and v are retained when the index is empty. Maps out of the proposed quotient are exactly compatible maps on all cone simplices, including the constant cone. Its A-action is specified and no two forward letters can compose. Thus this quotient computes the pushout directly; it does not invoke unjustified preservation of mapping sets.

Step 6 has no outside fact: the relations preserve f, and the two inverse maps on equivalence classes are given. I checked the indices in K(alpha) and Q(alpha), simplex operators, and precomposition. For K empty both mapping sets are empty. This is a step, not a new node restating the point-formula clause.

Step 7 cites only the Q^0=Delta^0 clause of pinched-cube-latching. The unique [n]→[0] coend relations identify all constant simplices with it. The formulas for changes of K, S and A specify exactly how naturality works (Fa=a'C[h]); they commute with the quotient relations and composition. Smallness follows from small sets of generators, countably many degrees, finite words and set quotients. No Kan, fibrancy, cofibrancy or quasicategory hypothesis has been imported from a source theorem.

I checked the small cases K=empty, K=Delta^0, K=Delta^1, X=empty, A with no objects, and a with noninjective vertex map. For K=Delta^1, the existing Q^1 quotient is the interval and the formula is A(-,b)×Q^1. An empty A permits only empty S and X, so there is no illegal vertex s to use in the point clause. The general collage still has its lone v. Nontrivial endomorphisms of b in A are retained in the first factor, not killed; only the identity-category image of the constant base is identified. These checks exposed no false statement, so no STATEMENT-DISPUTED repair is required.

Mathlib searches used msearch.py only. The first LeanFinder returned constant simplicial maps, unitors and standard-simplex infrastructure; the second returned profinite extension and ordinary cone results. Loogle returned the enrichment of simplicial objects for the first pattern and zero hits for the second. LeanSearch returned generic pushout universal properties and pointwise functor-category pushouts. I read the enriched-category instance and pushoutObjIso source to rule them out: neither gives the coherent realization or the pinched point formula. Both grep patterns had zero hits. All services were available. There is no exact match or one-line specialization, and no unrun query is recorded.

## Unfinished work

None in this split. The two existing dependencies remain their own items; this work does not split them or claim their stage-3 proofs.

## Validation

The required server dry run printed `OK (not pushed)` at a03eb76de5: preflight passed, including the DAG and split checks. Every citation excerpt was also checked locally for literal membership in the cited statement, and the item statement compared equal to the current repository statement. A final dry run is being run on this report and the tightened Step 7 excerpt, which now quotes the exact Q^0 clause it uses. No delivery is pushed; the second reader performs that step.

## Second reading by Q16

Independent second reader, 2026-10-17. Recovery condition checked: this is Q16, the stage-1 item JSON exists, and no stage-2 packet exists at the specified Q16 path. The ordinary stage-1 brief applies. No Lean was written and no compiler, Lake, local preflight or git command was run. The first worker's report and Review by Q16 remain above.

Statement: checked every hypothesis and clause against HTT §§2.2.1–2.2.2, printed pp. 73–76, read independently online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf; verdict PASS. Taking the source's category C to be A opposite gives exactly the stated variance, and the source identifies straightening at a vertex with the Q realization. The source does not impose Kan or fibrancy hypotheses on this construction. The unchanged statement's arbitrary-A product formula is justified by the explicit attachment argument, rather than claimed verbatim from HTT. Both cited dependency statements were read in full; only their stated constructions and cocompleteness are used. The current main-20261015 ancestor proof paragraph 2, historical unit record and chapter record were checked: this remains its foundational coherent mapping input, with no route change and no SGA proof citation.

Step 1: checked against interval-lifting's cocompleteness clause, pinched-cube-latching's defining simplex colimit, and HTT Example 2.2.2.5; PASS, the displayed mapping-out correspondence proves the required preservation.
Step 2: checked against the subset-poset formula and the degreewise word presentation's universal property; FIX, distinguished old simplices from mixed simplices and marked this substantial construction non-elementary. With that correction, old-endpoint relations restrict to initial faces, so the no-return argument is valid.
Step 3: checked each relation of the amalgamated word presentation for arbitrary object/arrow identifications under a; PASS, a word ending in A cannot visit v, and every old B-letter is replaced by its image in A. Composition supplies precisely the presheaf action.
Step 4: checked against HTT's definition of J and Q and pinched-cube-latching's identical definitions; FIX, the triangular structure of C[J^n] follows from Step 3 with base category {x}, rather than applying Step 2 directly to the pinched simplicial set. The unique final Q-letter normal form proves the product and respects all monotone maps.
Step 5: checked against the ordered-join simplex decomposition, Step 4 and HTT Remark 2.2.2.1; FIX, spelled out that maps on a simplex piece are determined on (id_b,q), with value on (f,q) given by composition with F(f). This explicitly verifies the compatible-family universal property and retains A and v for the empty index.
Step 6: checked both inverse maps against every generating coend relation, simplicial operator and old-arrow action; PASS, every relation fixes f, so the quotient separates as the displayed product, including empty K.
Step 7: checked against the exact Q^0=Delta^0 clause and the pushout/coend maps; PASS, the unique [n] to [0] relation computes Delta^0, and the formulas commute with precomposition and every parameter map satisfying Fa=a'C[h]. Small finite words and small quotients prove the universe clause.
New nodes: none; PASS, no restatement, duplicate, elementary child or leaf was introduced. Existing cone-presheaf-adjunction and unmarked-straightening-quillen do not state this point formula and supply downstream model/adjunction assertions; rigidification-boundary-cube treats a different attachment. None is needed or used here.

Edge cases: checked X empty, K empty, K=Delta^0, K=Delta^1, empty A, a collapsing two vertices, and a one-object A with nontrivial endomorphisms. PASS: empty K has no arrows into v but retains both A and v; Q^0 gives the representable; the first factor preserves arbitrary endomorphisms of b; empty A forces S and X empty. No statement dispute was found and no statement was changed.

Independent searches: ran msearch.py with a new semantic phrasing, a general enriched-colimits type query, and a full-Mathlib grep for rigidification, pinched, collage and straightening. LeanFinder returned simplicial enrichment/nerve/hom, ordinal tensor, Cech nerve and augmented-simplex infrastructure, not this theorem; Loogle's valid query and grep returned zero hits. A first malformed Loogle query was rejected; its actual diagnostic is recorded as an unavailable mathematical search, not evidence of absence. Searches and their actual logged results are appended to the item's mathlib_searches. No Mathlib leaf is warranted.

Changes: repaired the old-versus-mixed simplex wording in Step 2 and its elementary flag, corrected Step 4's reference to the pinched-pushout case of Step 3, expanded Step 5's mapping-out calculation, and recorded independent searches. All seven proof steps remain; no statement, dependency set, source route or existing citation was changed. The citations were rechecked verbatim against the current dependency statements, including the precise clauses each step uses. Backups of the item and report were retained before edits. The required server dry run and delivery follow this completed reading.
