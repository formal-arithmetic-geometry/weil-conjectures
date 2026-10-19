# Worker report: lem-coef-tensor-coend-skeletal-pushouts

## Files written

- `dag/nodes/sec-six-functors/lem-coef-tensor-coend-skeletal-pushouts.json`: statement unchanged, split into fourteen proof steps. No exact Mathlib match.
- `citations.json`: 33 verbatim statement quotations, one for every step/node pair.
- `searches.jsonl`: six actual N2 searches, with their returned status and digest. The item's pre-existing NM searches remain intact.
- `write_split.py`: sandbox-local authoring script; not a delivery file.

There are **0 new nodes and 0 new Mathlib leaves**. The proof is a direct universal-property calculation; its small auxiliary calculations are written out rather than turned into separate items. The required final dry run is recorded below when completed. Nothing is pushed by this worker.

## Attachments

None. Read-only searches of `WeilConjectures/` in slopmaster2 and upstream master for the exact item tag, coend, latching and skeletal terminology found no project declaration stating this formula. The broad realization hits concern unrelated adic realizations; they do not attach this item. Upstream master's unfinished material is not used as evidence of completion.

## WANTED

WANTED: Daniel Dugger, *A Primer on Homotopy Colimits*, formula (3.2), proof of Theorem 3.5, and Section 19.1, printed pp.9-10,90, for this item. Read the PDF online at https://pages.uoregon.edu/ddugger/hocolim.pdf on 2026-10-17, including the skeletal-square diagram on PDF page 10. There is no archived copy under this repository's literature directory. No download or literature-directory edit was made.

## What was wrong and what changed

The assigned node was initially absent from the read-only shared tree, then appeared during its normal synchronization. Its sandbox was initially empty of nodes, report, citations and searches. I copied the newly available unsplit node and retained its statement, existing six search records, source, ancestry, chapter and unit. There was no existing split to discard or repair. Its statement is mathematically correct; no STATEMENT-DISPUTED correction is needed.

The imported source identifies the intended formula but leaves its verification unstated. I supplied that verification by constructing the attaching maps and checking their restrictions, then proving extension and uniqueness against an arbitrary target. This is marked `proof_origin.by = agent`: Dugger supplies the method and the topological example, not this exact theorem in the stated arbitrary enriched category. In particular, I did not identify Dugger's topological latching subspace with the categorical latching object by assumption.

The potentially delicate mixed overlap is now explicit: for a proper surjection theta and proper face delta the two composites are q_a(1 tensor Delta^(theta delta)) and q_b(X(theta delta) tensor 1). Both indices are below n, so the existing lower-degree coequalizer relation equates them, even when theta delta has both a nontrivial surjective and a nontrivial injective factor. The proof does not require latching morphisms to be monic, a decomposition of X_n into degenerate and nondegenerate elements, or any model structure.

## Not duplicates

No node is created. Whole-DAG statement searches for coend, latching, skeletal pushout and boundary/colimit were inspected, together with whole-blueprint searches using `tools/blueprint_refs.py` for skeletal, coend, latching, tensor and realization. I opened the statements of the nearby `def-coef-simplicial-model-realization`, `lem-coef-enriched-coend-homotopy-invariance`, `lem-coef-cofibrant-subset-colimit-decomposition`, `lem-coef-injective-simplex-cocone-restriction` and `lem-weil-pbc-simplicial-hom-object-standard-simplex`. They respectively define the full coend, address enriched-module weak equivalences, address a different finite-subset diagram, address infinity-categorical cocones, and address semirepresentable matching objects. None supplies or supersedes this arbitrary tensor-coend pushout statement. The pre-existing ancestry is retained and `same_as` remains empty.

## Review by N2

I read the standing stage-1 brief, the stage document, delivery-errors B-E in full, the three SETUP levels, GOAL, dag-sync, the worker role, tools README and current state. I read the chapter and unit records and the current main-20261015 ancestor `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, especially its paragraph beginning “For K”. The item's existing historical binding is preserved. This is a foundational computation within its already established ancestry, not a replacement of a unit or chapter route. No SGA source is used.

For the mathematics I read Dugger's PDF at the places above; the local Stacks `categories.tex`, tag 002F, label `definition-colimit`; and `simplicial.tex`, tag 016A, label `definition-simplicial-object`, and tags 0174/0175, labels `section-simplicial-set` and `definition-terminology-simplicial-sets`. The source correctly remains Dugger plus an explicitly agent-written generalization, rather than a fabricated Stacks tag for the entire theorem. There are no new nodes requiring additional sources.

I opened the entire statements of all four nodes cited in the proof: `def-coef-simplicial-tensor-cotensor`, `def-weil-pbc-category-colimit`, `def-weil-pbc-simplicial-set`, and `def-weil-pbc-simplicial-object`. Their exact statement texts are the quotation evidence in citations.json. I checked the following uses against those statements.

1. The tensor definition supplies the natural representing isomorphisms and underlying-map interpretation. Step 1 constructs parameter maps and checks bifunctoriality by their unique transposes; it does not cite the definition for an unstated preservation theorem.
2. The same definition and the colimit definition give the explicit four-way correspondence of maps proving preservation in each variable. The cotensor is used for preservation in the object variable. Empty diagrams are included.
3. The simplicial-set definition supplies monotone maps and natural transformations, and the tensor definition turns maps to the mapping simplicial set into tensor maps. Step 3 proves the boundary gluing rule by the increasing enumeration of a map's image. Independence of a containing face and compatibility with precomposition are written out; no presheaf-colimit or density theorem is presumed.
4. The colimit definition applied to the two parallel arrows gives the exact family equations for R_N. The simplex definition establishes smallness of every indexing category used: finite degrees, the countable simplex category, and the countable sequential index. This does not use large-index colimits.
5. The simplicial-object definition gives contravariant functoriality; the tensor definition gives interchange; the colimit definition gives the latching extension. The equation for theta = rho theta' has exactly the arrow direction written in the item's latching category. The coequalizer relation is used only with a,a' below n.
6. The same statements, and the proved boundary rule of Step 3, give the boundary map. The formula for delta = delta' gamma checks all inclusions of proper faces, not merely adjacent codimension-one intersections. Again both indices are below n.
7. Those statements give the two actual overlap maps. Contravariant composition makes X(delta) X(theta) = X(theta delta), and the lower coequalizer relation applies to theta delta with no extra injectivity or surjectivity assumption. Tensor-colimit uniqueness and the boundary rule justify that testing these components suffices.
8. Tensor bifunctoriality gives the canonical left edge. The colimit definition and the degree-n coequalizer relations check commutativity on every latching component and proper face, hence on B_n.
9. The tensor and colimit definitions translate agreement of f and g on B_n into exactly the two displayed families of equations. Both necessity and sufficiency are proved using the two colimit component tests, so an unproved identification of matching or latching objects is not invoked.
10. The simplex definition allows the explicit increasing-image factorization alpha = delta theta; this is an elementary construction on a finite ordered set, not an appeal to an uncited factorization theorem. The simplicial-object and tensor definitions prove the displayed four-term calculation for the composite relation. This covers arbitrary degree-n endomorphisms as well as maps with one endpoint below n.
11. The colimit definition gives the unique h and proves equality with f on R_(n-1) by its summands. This step is marked non-elementary as the assembly of the full pushout conclusion; its actual argument has already been exposed in Steps 4-10, rather than relocated into a new node or hidden behind a definition citation.
12. The simplex, tensor and colimit definitions give the separate n=0 check, with empty latching and boundary diagrams and an identity relation.
13. The colimit statement supplies both comparison maps. The backward map's equation for alpha is checked in the single finite stage max(a,b). Both composites are checked on the defining summands and then the sequential cocone; no uncited interchange-of-colimits theorem is used.
14. The simplicial-object definition states the exact naturality equations for u. Tensor functoriality and colimit uniqueness then give all maps of squares and naturality of the comparison isomorphism. The proof spells out both face and degeneracy equations.

These are complete elementary calculations relative to the cited definitions, with the conclusion assembled in Step 11. In particular C1/C4 and D3 were checked against the actual formulas, not just by checking that a dependency exists. There is no hidden non-elementary fact to put into a new node. Every step is under 1100 characters, so no non-elementary step reaches the human's 2000-character review threshold. No extra hypotheses are introduced. Definitions and the existing Mathlib colimit and simplicial-set/object leaves are legitimate generic tools; no off-unit statement theorem is cited.

Small cases checked independently: n=0 gives the initial pushout into X_0 tensor Delta^0. At n=1, the sole proper surjection has target [0], the boundary has its two vertices, and each mixed composite is the identity of [0]; its agreement equation is therefore exact. At n=2, a constant endomorphism [2] to [2] factors through [0], and an endomorphism with image {0,2} factors through [1], so Step 10 handles all previously easy-to-miss endomorphism relations. More generally a constant diagram in simplicial sets, tensored by cartesian product, has R_0 = A and R_n = A at all higher degrees: the latching category has the constant surjection to [0] as an initial object and hence its constant diagram has colimit A. The constant initial diagram gives only initial objects. The proof permits non-monic latching arrows and uses only the common-source overlap, never set-theoretic intersection inside X_n.

All six actual N2 Mathlib searches were read. The two LeanFinder phrasings and LeanSearch return ordinary Kan-extension skeletons and set-valued cells; Loogle gives zero hits; the AlgebraicTopology grep gives realization and skeletal-category material, and the CategoryTheory grep gives general coends. I read the relevant pinned source: SimplicialObject/Basic.lean:286-310 (ordinary Kan-extension skeleton); SimplicialSet/Skeleton.lean:425-454 (simplicial-set relative cells); SimplicialSet/Boundary.lean:33-79 (non-surjective-simplex boundary); SimplicialCategory/Basic.lean:18-29 (simplicial tensors still a TODO). These do not state this item in a one-line specialization. The old NM search evidence is preserved rather than rewritten or attributed to N2.

B1-B9 were checked: no new nodes, no proof concealed in a statement, explicit objects and map types, single-escaped TeX, exact source places, and genuine search provenance. C3 is avoided by taking only the cited statements, not their proofs. D1/D2 are avoided by creating no restatement nodes. E1-E5 were checked through the degree bounds, contravariance, composite-map calculation and explicit inverse. The sandbox contains no Lean source, and no compiler, Lake command or local DAG/preflight checker was run.

## What remains

Only the independent second reading and delivery remain after the required dry run accepts the split. No mathematical subtask of this split has been deferred, and no attachment or statement dispute is pending.

## Second reading by N2

- Statement: checked the complete coend, latching-object, boundary pushout, sequential-colimit, and naturality clauses against Dugger, Formula (3.2), the proof of Theorem 3.5 (pp. 9–10), and the tensor extension discussion in §19.1 (p. 90); all hypotheses and edge cases are present and the categorical generalization is explicit.
- Step 1: checked the tensor representing isomorphism, induced simplicial-set maps, identities, composition, and interchange against `def-coef-simplicial-tensor-cotensor`; verdict correct and elementary.
- Step 2: checked both colimit-preservation arguments via the tensor/cotensor adjunction and the colimit universal property in `def-coef-simplicial-tensor-cotensor` and `def-weil-pbc-category-colimit`, including initial objects; verdict correct and elementary.
- Step 3: checked the increasing-image factorization of boundary simplices and compatibility under face inclusions against `def-weil-pbc-simplicial-set` and the tensor adjunction; verdict correct and elementary, including n = 0.
- Step 4: checked the coequalizer family equations, truncation maps, and smallness claims against `def-weil-pbc-category-colimit` and `def-weil-pbc-simplicial-set`; verdict correct and elementary.
- Step 5: checked latching factorization, contravariant arrow directions, and the induced colimit map against `def-weil-pbc-simplicial-object`, tensor bifunctoriality, and colimits; verdict correct and elementary.
- Step 6: checked proper-face compatibility and all face intersections against the simplicial-object equations, simplicial-set boundary calculation, tensor, and colimit definitions; verdict correct and elementary.
- Step 7: checked the mixed overlap composites, including non-injective/non-surjective `theta delta`, against the lower-degree coequalizer relation and contravariant composition; verdict correct and elementary.
- Step 8: checked the canonical latching and boundary maps, their common-source agreement, and square commutativity against tensor bifunctoriality and the colimit pushout property; verdict correct and elementary.
- Step 9: checked the exact surjection and injection equations characterizing agreement on `B_n` against the pushout and colimit universal properties; verdict correct and elementary.
- Step 10: checked image factorization of every monotone map, including nonidentity endomorphisms, and the tensor interchange calculation against the simplicial-set/object definitions and colimit relations; verdict correct and elementary.
- Step 11: checked existence and uniqueness of the extension `h : R_n -> T` and its restrictions against the coequalizer universal property; verdict correct and complete (the sole non-elementary assembly step).
- Step 12: checked the empty latching and boundary diagrams and the identity-only degree-zero relation against all three cited definitions; verdict correct and elementary.
- Step 13: checked the compatible maps in both directions between the sequential truncation colimit and the full coend, with `N = max(a,b)`, against the colimit universal property; verdict correct and elementary.
- Step 14: checked naturality on coend, latching, boundary, pushout, and comparison maps against `def-weil-pbc-simplicial-object`, tensor functoriality, and colimits; verdict correct and elementary.
- New nodes: none; therefore B1–B7, duplicate checks, source checks, and Mathlib-leaf checks have no new-node cases. The existing four dependency statements were opened in full and their exact quotations remain in `citations.json`.
- Changes: none. No statement correction, dependency change, proof repair, citation repair, or search-record repair was needed.
