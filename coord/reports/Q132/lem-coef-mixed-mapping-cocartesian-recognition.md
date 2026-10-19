# Q132: lem-coef-mixed-mapping-cocartesian-recognition

## Files written

- `dag/nodes/sec-six-functors/lem-coef-mixed-mapping-cocartesian-recognition.json`: statement node, split in seven steps; no exact Mathlib match. The statement and its three statement dependencies are unchanged.
- `citations.json`: one verbatim statement extract for every step/node pair. Resumption replaced several narrow extracts by the actual mapping-space, fiber, associativity and invertible-component clauses used.
- `report.md`: this report. Existing `searches.jsonl` is retained unchanged; the inherited and already logged item searches are retained in the node.

## New nodes

None. Zero Mathlib leaves. The non-elementary ingredients already have DAG nodes, and the inverse calculation is a few lines in their homotopy category, rather than another recognition lemma restating this item.

## Attachments

None. A search in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, mixed mapping spaces, and cocartesian representability found no project declaration stating the item. The existing base record has no declaration to attach. Nothing from upstream master is treated as a finished proof.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 2.4.4.3 and its proof, printed pp. 131–132, Definition 2.4.2.1, and Corollary 2.4.1.6, archival copy in literature/, for lem-coef-mixed-mapping-cocartesian-recognition. I read the Harvard-hosted PDF online, including its warning that the homotopy-pullback square requires its specified coherent comparison.

WANTED: Kerodon, Subsection 4.6.8 (01PF), especially Construction 4.6.8.9, Remark 4.6.8.10, Propositions 4.6.8.11–12 and Notation 4.6.8.15, and Construction 3.6.5.1 (0148), archival copies for the composition and simplicial-homotopy tools used here. These were read online. Tag 00UB returned an internal error on resumption; the accessible realization construction 0148 and, decisively, the existing homotopy-equivalence node's full statement supply the interface this delivery uses. Kerodon tags are not Stacks tags; no Stacks result states this quasicategorical recognition theorem.

## What was wrong or incomplete

The repository item is statement-only. Its source already calls for the represented specialization of the general cocartesian mapping criterion; that specialization needs an actual proof. The sandbox preserved from the interrupted turn had seven proof steps and searches but no report. There was no running Q132 delivery process on resumption. I compared the copy with the current repository: the statement, chapter/unit, blueprint ancestry and creation stamp still agree. I retained all previous proof text and recorded queries/results.

The first citation record quoted only the standard-simplex paragraph and a lift-existence definition, although the first step also uses the right-pinched mapping model and fiber definition. Several later records quoted only component-dependence of precomposition, whereas the steps also use associativity, units, edge representatives, and the inverse-triangle criterion. Those are present in the same cited statements; citations.json now quotes the needed passages. This is a citation repair, with no change of theorem or proof route.

No statement dispute was found. In particular, no functor from C to D and no naturality in x is necessary: coherent naturality in y is exactly what identifies precomposition after applying epsilon. Assuming merely objectwise equivalences without that naturality would not justify Step 3; the item explicitly includes the necessary higher-parameter compatibility.

## What remains unfinished

No part of the one-level split is left unwritten. The general cocartesian mapping criterion remains a dependency for its own worker, not something silently proved or attached here. Literature archival requests above remain open. Validation and delivery results are recorded below after the commands finish.

## Blueprint and route

I read the chapter and unit records and the current-brief snapshot `main-20261015`'s integral exceptional-adjoint proof. The ancestor `prop-coef-integral-exceptional-adjoint`, proof paragraph 2, is the middle finite derived mapping-complex adjunction before the inverse limit. The preserved ancestry chain reaches the coherent-module section model's former Step 4. This delivery supplies precisely its recognition of transport from represented mixed maps; it does not replace the coefficient-adjunction route or alter any unit realization. This is a supporting lemma, not the unit's statement node.

`tools/blueprint_refs.py ancestor` confirms that ancestor. The whole-blueprint search for cocartesian returned no imported blueprint match. Whole-DAG keyword searches locate the general mapping criterion, mapping composition and identity-edge statements already cited. No new node is created. Thus no new-node same-tag pairs require a Not duplicates distinction. The item's same_as remains empty.

The sole off-unit statement used is `lem-cbc-simplicial-homotopy-equivalence-weak`. It converts the explicit simplicial inverse homotopies of Step 4 to weak equivalences after realization. This is a general tool, declared in split_report.tool_uses; the same-unit composition theorem gives the homotopies but does not state this realization conclusion. All other proof statement nodes are in the item's unit. The chapter's inherited reference list is not a source citation of this split; no prohibited SGA route is used.

## Mathlib search review

I read the preserved searches.jsonl and the actual returned names before reusing the queries. There are already several semantic phrasings, Loogle, and source greps, so no identical remote search was repeated. Fresh Q132 queries in the preserved attempt include both the interval recognition statement and the possible precomposition criterion. The semantic hits are ordinary-category IsCocartesian/IsStronglyCocartesian, Grothendieck transport, ordinary Yoneda, or the quasicategory horn-filler interface. The source greps do not locate the represented coherent mapping-space assertion. I re-read Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean at the IsCocartesian and IsStronglyCocartesian definitions (lines 48–75) and ordinary isomorphism instances. Ordinary uniqueness of factorizations is not the required equivalence of all coherent mapping spaces. The ordinary Yoneda inverse calculation is written directly in Step 5 and needs no new leaf. The inherited invalid Loogle identifier is recorded as a query error, with its corrected successful query preserved; it is not represented as evidence of absence.

## Review by Q132

I checked delivery-errors B through E against the item and each dependency statement, rather than relying on a tag or on a dependency's proof. I read HTT Proposition 2.4.4.3 and its proof online and checked its hypotheses: p is an inner fibration, E and the interval are quasicategories, and the criterion applies before any cocartesian lifts have been constructed. Its opposite gives the orientation used here. The item is the represented interval specialization, with the additional inverse calculation written out by the agent, so proof_origin.by stays agent. I also read HTT's identity-edge corollary and fibration definition and the accessible Kerodon composition statements. There are no new nodes for which a new source or untested assertion is being introduced.

1. Step 1 uses the complete right-pinched mapping-space and path-space homotopy-fiber definitions in def-cbc-enhanced-diagrams-cones and the horn/fiber definitions in def-coef-infinity-fibrations. An inner horn over a constant vertex fills within that fiber. A monotone map to [1] whose endpoints are equal is constant. This computes all four base mapping spaces and the same-fiber and forbidden-color spaces directly, degree by degree. The only base path space used is that of a point. This is an elementary calculation from the cited definitions.
2. Step 2 uses exactly the square stated in lem-coef-infinity-cocartesian-mapping-criterion. For a test vertex over 0 its upper-left and lower-left spaces are empty and its lower-right is a point, giving an empty path-space pullback. Over 1 both lower corners are points, so the pullback is the mixed mapping space. Thus the cited general theorem genuinely gives the displayed precomposition equivalences. Its statement assumes no other lifts, so this is not circular.
3. Step 3 uses the canonical composition and component-dependence clauses of lem-coef-infinity-mapping-composition. The needed homotopy with domain the entire mapping space, including higher simplices, comes from the hypothesis of coherent naturality of epsilon, not from an uncited Yoneda theorem. Two-out-of-three here is the direct composition calculation on components and based homotopy groups. I checked that the two maps have the same source and target after applying epsilon.
4. Step 4 uses associativity and units of the same composition node and its inverse-edge criterion, then the full statement of lem-cbc-simplicial-homotopy-equivalence-weak. The domains of b-star a-star and a-star b-star are respectively Map(y,z) and Map(T_x,z). Both are simplicial homotopies of precisely the form required by the weak-equivalence tool. The tool assumes neither nonemptiness nor Kan fibrancy, so empty mapping spaces cause no omitted hypothesis.
5. Step 5 uses the component category and equivalence criterion explicitly stated in lem-coef-infinity-mapping-composition. Surjectivity at z=T_x gives b a=1; injectivity at z=y applied to (a b)a=a forces a b=1. The statement of that node then supplies equivalence-edge witnesses. This is the elementary two-object inverse proof; I did not introduce a child merely restating the item's recognition clause.
6. Step 6 uses the edge-representative and identity-component assertions of the same node. Surjectivity of epsilon on components provides a mixed edge with the exact endpoint T_x. Step 1 removes any extra base-path data since Map(0,1) is a point. Its represented identity class is invertible, so the previous implications give a cocartesian lift. This does not replace a specified target by an unspecified equivalent object.
7. Step 7 takes only the degenerate-edge clause from lem-coef-infinity-cocartesian-composition-initiality, whose statement I read, and the lift-existence definition from def-coef-infinity-fibrations. The interval has exactly its two identities and one mixed edge. Degenerate edges and Step 6 therefore cover all base edges and all their sources. No transport-composition or initiality assertion from that tool is silently needed.

I tested the empty and small cases explicitly. C empty allows arbitrary D and leaves just identity lifts. D empty forces C empty through the assumed T_x, rather than producing a false lift. With both fibers terminal the represented mixed mapping spaces are contractible and every mixed edge satisfies the mapping criterion. For nerves of ordinary categories the calculation becomes the usual Hom factorization and invertibility test. Noninvertible represented arrows fail one of the two component tests in Step 5. Arbitrary higher mapping spaces are retained in Step 3; this is not an argument merely about their components except for detecting equivalence after Step 4. All non-elementary ingredients have existing cited nodes. Every proof step is below 2000 characters; none hides a separate long comparison. JSON escaping, union of proof uses, preserved metadata, blueprint origin and all ten citation pairs were checked. All work stays in the sandbox; no Lean was written and no compiler or build was run.

## Validation

The server-only `srvcheck.py ... review_split` exited 0 with PASS, zero new nodes, and the declared simplicial-homotopy tool use accepted. The first full `deliver.py ... --no-push` exited 0: `OK (not pushed)` at ae0231ede2, preflight passed. That preflight includes the DAG and split checks. This report addition is followed by the final dry run before pushing; the final command output gives the delivered commit.
