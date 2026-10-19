# NV: lem-coef-module-scalar-restriction-mapping

## Files written

- `dag/nodes/sec-six-functors/lem-coef-module-scalar-restriction-mapping.json`: statement, split into eight proof steps. Mathlib verdict: no match. The statement, source, ancestry, chapter, unit and inherited searches are retained. The five searches actually run in this sandbox are appended.
- `citations.json`: one exact statement quotation for every step/node citation.
- `report.md`: this report. No new DAG nodes, no Mathlib leaves, no unit or chapter edits, no Lean edits or compiles.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures tree for the exact blueprint tag and for scalarRestriction, scalar_restriction, LM, quasicategories and left-tensored language. The broad coherent-module search returned ordinary quasi-coherent algebraic geometry. No project declaration states the coherent module-transformation mapping comparison. Upstream master is reference material, not proof evidence.

## WANTED

WANTED: Lurie, Higher Algebra, September 18, 2017, Definitions 4.2.1.7, 4.2.1.13 and 4.2.1.19 and Corollary 4.2.3.2, for lem-coef-module-scalar-restriction-mapping. The source is available at https://people.math.harvard.edu/~lurie/papers/HA.pdf and was read online; it is not archived under literature/. No download or live-project edit was made. No Stacks tag states this infinity-operadic assertion.

## Findings and scope

No statement dispute. The assertion is true with the indicated operation data. It would be wrong to infer it merely from binary action equations, or from a bijection of ordinary module maps. It would also be wrong to recover g from hg when h is not faithful. The target comparison is over the space of retained g's, with target pulled back along composition with h; fixed algebra-component spaces retain the homotopies specifying their components. These are clarifications of the existing mapping-space assertion, not extra hypotheses.

The parent lem-coef-module-operad-encoding uses this item to establish its cartesian-fibration conclusion. Its conclusion cannot be used here. This split proves the operation-data comparison directly and does not cite that parent. The existing scalar-restriction-coherence node supplies the specific all-tree endpoint comparisons; the existing reconstruction node supplies the operation/section dictionary. The proof constructs and compares the transformation data themselves, and checks which map reconstructs to postcomposition.

The current unit has no recorded proof steps; this is a created descendant of prop-coef-integral-exceptional-adjoint. I read its blueprint proof paragraph 2 (the middle derived mapping-complex comparison) in main-20261015. The item serves the operadic foundation of that comparison through its retained ancestry; I have not changed the unit route or its realized fields. The generic off-unit tools are declared in split_report.tool_uses, not in a maintainer-owned tool_uses field.

## Searches and reuse

The sandbox initially contained only dispatcher brief markers, no node, report, citations or search log. There was no active deliver.py or msearch.py invocation for this item. There was therefore no previous mutation or search result to repeat. All existing item searches from its repository record remain intact.

I ran msearch.py with LeanFinder, Loogle, LeanSearch and source grep, followed by a second LeanSearch phrasing. The five exact queries and result summaries are appended to mathlib_searches and appear in searches.jsonl. The results concern ordinary ModuleCat restriction/composition, ordinary monoidal module homomorphisms, extension/restriction adjunctions and ordinary IsCartesian. I read Mathlib/CategoryTheory/Monoidal/Mod.lean:363-415: scalarRestriction_hom is at 387-396, its alias at 445. It does not describe quasicategorical mapping spaces or higher contraction data, so it is not a leaf for this item.

Before deciding whether any helper was missing, I searched the full DAG by operation/tree/contraction, boundary transport, path transport and coherent limits; I opened the statements of the relevant candidates. I ran blueprint_refs.py search for scalar restriction, coherent transformation and boundary transport: no blueprint matches. The ancestor command gives prop-coef-integral-exceptional-adjoint, agreeing with the retained blueprint.from field. Existing generic Kan-space lemmas suffice, so no new node or duplicate was introduced.

## Review by NV

I read the standing stage-1 brief, stage document, worker role, SETUP's three blueprint levels, GOAL, dag-sync, the item chapter/unit records and delivery-errors B through E in full. I read Higher Algebra's ordered-fiber LM construction and Definitions 4.2.1.7, 4.2.1.13 and 4.2.1.19 online. These establish the precise two-color, ordered, one-module-input setting. Corollary 4.2.3.2 (printed p. 527) confirms the expected result without a presentability hypothesis, but is deliberately not a premise of the split. The detailed operation-data proof is marked agent-written, with the archived blueprint ancestor as proof_origin.document. No SGA source is used.

I opened every cited node and read its statement. For step 1, colored-operation-section-reconstruction explicitly reconstructs transformations from color maps and operation-naturality/higher substitution simplices, including arbitrary parameters. The left-module definition identifies the category of operators, algebra restriction and module sections; enhanced-diagrams-cones defines the homotopy fibers used when fixing g. No fully-faithful-only result is substituted for a transformation-space result.

For step 2, scalar-restriction-coherence states the formula for every r, the unit condition, and the transformation with algebra component h and module component identity. Substituting g and f in that formula gives the actual endpoint path sigma_r. The tensor/action composition constraint is specified by the left-module definition, so no strict equality of parenthesized tensor products is assumed.

For step 3, the coherence node explicitly supplies all chains of contractions, grafting, permutations and identity insertions, and identifies how they are evaluated on pure-algebra subtrees and the unique module branch. Precomposing by g and f gives the same endpoint prisms on all faces. Reconstruction explicitly makes a forest the product of output trees and omits inputs sent to the basepoint. I retained subinterval operations before discarded branches disappear; merely dropping the entire discarded branch would miss earlier faces.

For step 4, enhanced-functor-cone-calculus supplies Kan mapping spaces, not contractible mapping spaces. The pushout-product lemma applies to P included in Q and the endpoint horn included in Delta^1, with target Z mapping to a point; Z being Kan is exactly the lifting hypothesis. Inserting arbitrary boundaries of parameter simplices in P gives a boundary lifting property for the space of extensions. The Kan-fibration fiber criterion identifies this extension space as contractible. This is why a coherent boundary change can be made relative to previously fixed faces, even when the original spaces of operation comparisons have many components. The proof does not assume that an arbitrary sphere in Z fills.

For step 5, the operation and contraction indexing data come from reconstruction; scalar-restriction-coherence provides their compatible boundary prisms. The same pushout-product calculation is performed relative to faces already fixed, rather than taking separate noncompatible fillers on individual trees or individual parameters. The core/Kan lemma says every edge of a Kan complex is invertible, which justifies reversing sigma and the higher endpoint homotopy. Neither h nor g is required to be invertible. The reverse comparison receives g as part of the pullback data.

For step 6, mapping-composition supplies the composition classes, their identity and associativity homotopies and inverse witnesses; the core/Kan lemma makes these applicable to the endpoint paths. The relative prism calculation supplies the higher compatibilities of the inverse homotopies. I checked that the contraction fixes the underlying f and retained pure-algebra component throughout. Empty transformation spaces are allowed, because no initial module map is selected.

For step 7, the coherence node states the transformation data of e_h, and reconstruction covers transformations and all higher compatibilities. The composite naturality prism has exactly the previously constructed sigma as its second factor. Thus this step identifies the particular forward map with postcomposition; it does not infer that two abstractly equivalent spaces have the required comparison map.

For step 8, both operadic nodes explicitly include arbitrary simplicial parameters and restriction of parameters. The forward map is composition of transformations, so its source naturality is the coherent associativity of pasting. The enhanced-functor calculus supplies the componentwise-equivalence criterion in a functor category; this gives a coherent natural inverse after establishing the componentwise equivalence, without assuming an artificially strict natural choice of individual horn fillers. All sizes can be placed in one larger universe, as the cited definitions permit. No source limit or colimit, categorical-smallness change, presentability, or cartesian-fibration assertion for Theta is used.

I tested r=0, r=1, the identity algebra map, an algebra map that identifies distinct g's, trees with several successive module vertices, pure-algebra trees, empty tuples, forests with several module outputs, discarded branches, empty spaces of maps, and an arbitrary simplex of g's including its degeneracies. For h the identity the endpoint prisms are the unit constraints and the comparison is homotopic to the identity. For a nonfaithful h, retaining g prevents a false claim of injectivity on algebra maps. No assertion about existence of a module map for every underlying f is introduced.

I checked B: no new unsplit nodes or hollow definitions, TeX has single mathematical backslashes, no fake searches or invented tags. I checked C: every cited statement was opened; citations.json contains literal substrings; the two generic off-unit tools are declared, and a read-only traversal found no dependency path back to this item. I checked D: the steps carry the endpoint calculation, the relative lifting argument and the inverse comparison; the item is not relabeled as a new node. I checked E: the one-module-branch hypothesis is exactly the LM ordered-fiber rule; units and higher parameters are retained. There are no proof steps longer than 2000 characters. I reviewed the relative prism argument explicitly for hidden lemmas: it is the displayed pushout-product specialization of the existing generic lifting lemma, with the parameter boundary calculation written out.

## Not duplicates

No new nodes. The scalar-restriction-coherence node constructs the operations and e_h; it does not assert the mapping equivalence. Reconstruction states the operation/section dictionary; it does not assert this scalar comparison. Both are cited in their actual roles. No duplicate-tag pairs arise.

## Unfinished work

None in the one-level split. The cited unsplit lemmas remain their existing DAG items. Final server dry-run and push results will be recorded below.
