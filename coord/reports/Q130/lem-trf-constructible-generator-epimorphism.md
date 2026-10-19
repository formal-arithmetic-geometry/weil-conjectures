# Stage-1 report: lem-trf-constructible-generator-epimorphism

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-constructible-generator-epimorphism.json`: repaired split; no statement change.
- `citations.json`: verbatim citations for every non-elementary dependency used by every proof step.

## Attachments

None. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` stating the item exactly.

## WANTED

None. The Stacks sources used here are present locally.

## Not duplicates

No new node remains after the repair: the generic free-generator assertion was folded into Step 1. Step 1 cites the existing affine separating-family node and the existing module-colimit node, so it does not introduce a restatement of either item clause.

## Source and repair

I read Stacks Modules on Sites, Lemma 093B(2) in Situation 0937 (the arbitrary free epimorphism), and Etale Cohomology Lemma 095N (the finite-subfamily argument, lines 12412–12466). The source field and proof origin now cite 093B(2) in Situation 0937; the previous Tag 0CAH citation was wrong. I also read the statements of every cited DAG node and the current `blueprint_update` for `lemma-weil-pbc-geometric-stalk-conservative`.

The returned helper node was redundant with the existing affine separating-family route, so its argument is now explicit in Step 1: the affine rank-one family is separating, the module-colimit statement supplies its coproduct and the right-cancellation argument proves its epimorphism, and the affine-source, etale, and finite-type definitions supply the geometric properties of its members. The item's blueprint ancestry retains `lem-trf-constructible-free-etale-resolution`.

## Review by Q130

Step 1 uses `lem-weil-pbc-affine-etale-rank-one-separating` for its precise affine family, with all objects, coefficients, indices and Hom sets in its stated universe. The coproduct exists by `lem-weil-pbc-module-sheaves-colimits-forgetful`(2), applied to the discrete category of pairs (U,h); no large indexing category is used. The step writes out right cancellation with the coprojections, rather than citing the proof of the constructible-generation node. `lem-weil-pbc-affine-source-morphism-separated` gives separatedness, and `lem-weil-pbc-qcqs-morphism-permanence`(1) applies because the source is affine and the Noetherian target is quasi-separated. It supplies finite presentation; hence local finite type together with quasi-compactness is finite type by `def-weil-finite-type-morphism`. This repairs the implicit quasi-compactness inference.

Step 2 uses the existing extension-by-zero constructibility node for each summand, the Serre closure theorem for finite sums, and the constructible surjectivity-locus node. Thus each failure locus `T_J` is constructible under the hypotheses in force.

Step 3 now explicitly passes from module sheaves to abelian sheaves using `lem-weil-pbc-module-sheaves-colimits-forgetful`, which states faithfulness, exactness, and preservation of colimits. It also cites `lem-kun-stalks-commute-colimits` for the stalk of the coproduct and `prop-weil-pbc-geometric-stalks-exact` for surjectivity on geometric stalks. The finite generation hypothesis is exactly the statement of `lem-weil-pbc-constructible-module-finite-stalks`; finite support in a coproduct then gives one finite subfamily for each geometric point. Both p and q have surjective stalks: target generators lift first to M through p, then to the coproduct through q. This also corrects the earlier wording that skipped p.

Step 4 uses the spectral-space statement and the finite-intersection compactness statement exactly as quoted. The inclusion `T_{J_0}\subseteq\bigcap_kT_{J_k}` follows because enlarging a finite family only adds generators.

Step 5 uses the exact forgetful functor to identify the module cokernel with the abelian cokernel, and exact geometric stalks to compute its stalks. I explicitly use the blueprint-updated conservative statement at the geometric point over the algebraic closure of each residue field `\kappa(s)`, then apply its stalkwise criterion to conclude that the cokernel is zero and the map is epic.

Step 6 is the inclusion followed by the arbitrary free epimorphism, finite reindexing, and the finite disjoint-union identification. The latter now has its local argument written out from `def-weil-pbc-etale-sum-extension`: a lift into the disjoint union partitions the test object into clopen pieces. Coefficient sections split on that cover by the sheaf axiom; the two summand maps are inverse locally and hence after sheafification. `lem-weil-pbc-scheme-coproduct-family` supplies exactly the clopen disjoint components, and `lem-weil-pbc-module-sheaves-colimits-forgetful`(2) supplies the sheafified coproduct. Thus no equality of the raw presheaves on disconnected test objects is incorrectly asserted. The empty family and zero target were checked.

I checked the edge cases `X=\emptyset`, `C=0`, empty index set, and `p` an isomorphism. No Lean files were written, and no compiler, Lake, or build tool was run.


## Returned points repaired

- C1: Steps 3 and 5 explicitly cite the exact, faithful module-to-abelian forgetful functor, and Step 3 cites arbitrary colimit preservation by geometric stalks. Step 5 now names the algebraic-closure point of each residue field, following the conservative node's `blueprint_update`.
- B5: The erroneous topological-space Modules Tag 0CAH is removed from all delivered files; the correct source is Modules on Sites 093B(2) in Situation 0937, read alongside 095N.
- B7: All inherited search records and raw `searches.jsonl` records are retained. I read the generic presheaf generators and local-surjectivity hits, and ran the corrected search command without the extra `Mathlib` subdirectory. It returns 25 hits for `GeneratingSections|freeYoneda`, including `ModuleCat/Presheaf/Generator.lean:19,24,26`, and 15 hits for `isLocallySurjective_iff_epi`, including `Condensed/Epi.lean:47,63`, `CategoryTheory/Sites/LocallySurjective.lean:378`, and `Sites/EpiMono.lean:124`. None is the finite constructible lifting theorem. Earlier zero-hit grep calls had an extra directory prefix and are recorded as invalid searches superseded by these corrected calls; no fabricated hit is placed in their raw results.
- B9 and C5: The returned helper is removed from the sandbox delivery because it follows from existing statements by the cancellation argument now written in Step 1. Consequently no new-node ancestry remains to repair; the item's own ancestry still includes `lem-trf-constructible-free-etale-resolution`. This repair adds zero nodes and zero Mathlib leaves.
- Step 6: The finite disjoint-union extension identification now has explicit construction and sheaf-gluing citations and an argument; its componentwise geometric properties are checked on the disjoint finite open cover.

I compared the preserved item with the current shared copy: its statement, statement dependencies, chapter, unit, original creation data and blueprint fields are unchanged. The current main still has the item unsplit. The parent uses the lifting through an arbitrary epimorphism, and this clause is preserved. All six steps are shorter than 2000 characters. The argument introduces no hidden non-elementary helper: Step 1 is the elementary categorical cancellation; Step 6 is the local direct-sum calculation from the stated construction and sheaf axiom. No unresolved work remains in the split.
