## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-atlas-open-refinement-pullback.json: item, statement, split using existing nodes only; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each of the item's 17 step/node citations.
- searches.jsonl: five actual msearch.py queries and their results; previous searches in the item's imported record retained.
- report.md: this report.

No new nodes; zero new Mathlib leaves. The item statement, statement dependencies and blueprint provenance are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, AlgebraicSpace, algebraic-space terminology and atlas/refinement terminology. No declaration states every clause of this item. Related scheme gluing/atlas files do not have this sheaf-target conclusion. Existing Sheaf declarations are not attachment evidence and the parent affine-etale-cover node is not used in the proof.

## WANTED

None. Sources needed for this proof are present in literature/stacks-project.

## Findings and changes

The item was statement-only in the live DAG and there was no earlier sandbox split or search log. Read its chapter and unit records and the current main-20261015 lem-a1-affine-hc0 source. The item's existing blueprint ancestry supplies the algebraic-space construction used below the support/lissity argument; this work retains that route and proves its 03FX input without assuming the larger parent result.

Read Stacks spaces-properties.tex Tag 03FX, lemma-cover-by-union-affines, including the proof's prescribed atlas, open refinement, coproduct and composition. Expanded its scheme-test argument and its field-valued point consequence. Also read Tags 03BU and 03BV (definition-points and lemma-scheme-points), Schemes 01J9 (lemma-characterize-points), 01JR (lemma-open-fibre-product), 01HI (lemma-restrict-map-to-opens), 01IT (lemma-basis-affine-opens), and Morphisms 02GJ and 02GN (lemma-etale-characterize and lemma-composition-etale). Tag-to-label correspondences were checked against tags/tags. No source or statement correction was required.

Actual Mathlib searches used leanfinder twice, leansearch, loogle and grep through msearch.py. Read the returned types: sigmaOpenCover and sigmaOpenCover_X describe scheme coproduct covers; scheme IsEtale stability and etalePretopology describe scheme morphisms; affineCover and affine refinements concern scheme affine covers. The second leanfinder phrasing returned finitary extensivity, disjoint scheme coproducts and binary coproduct pullback squares, which do not directly state the algebraic-space target with arbitrary set-indexed summands and field-valued point classes. Read Mathlib/AlgebraicGeometry/Limits.lean, sigmaOpenCover at line 241, and Cover/Open.lean, affineCover at line 53. Thus the item is not a one-line Mathlib specialization; its component ingredients already have DAG nodes.

Searches of the entire DAG by title and statement, and blueprint_refs.py search for atlas, coproduct, open covering, disjoint union, 03FX and affine opens, found no existing node stating the entire item. Reused the existing general nodes rather than creating elementary, duplicate or clause-restatement nodes. In particular the general sheaf-coproduct comparison nodes in sec-trace-formula introduce additional sheaf-coproduct data; the direct sectionwise proof here needs only existing scheme gluing and coproduct facts. blueprint_refs.py ancestor confirms lem-a1-affine-hc0. No proof step exceeds 2000 characters and no inline comparison is being hidden behind a new statement-only node.

## Unfinished

No mathematical part remains. The delivery is a stage-1 natural-language proof, with no Lean writing or compilation. Independent review remains with the maintainer.

## Not duplicates

No new nodes were created. The parent lem-a1-space-affine-etale-cover depends on this item, so using it here would be circular; it is not cited. The sibling affine-atlas-open-cover likewise is not used. Existing general scheme coproduct, gluing, point factorization, affine basis and etale locality nodes are reused.

## Review by Q07

I checked the unchanged statement against the actual proof of Stacks 03FX, which starts with an arbitrary prescribed surjective etale atlas, allows an open refinement and gives the affine-base option. I read the statement of every node listed in each step's uses and copied the relevant sentences into citations.json. In particular, representability and surjective etaleness are taken from the scheme-test definition in def-trf-algebraic-space, rather than inferred from a definition of an atlas alone.

Step 1 uses that definition to obtain the represented surjective etale P over every test T. def-pc-fibre-product supplies existence and uniqueness for P_i. The precise open-image formula of lem-weil-pbc-open-fibre-product, applied over V with the second map the identity, identifies P_i with the inverse image of U_i, so these are a covering without any affineness assumption. The coproduct node states existence, its mapping property, disjoint open components and coverage. I added the citation of lem-pc-zariski-coverings-are-fppf after checking C1: using equality of E-sections on this Zariski cover needs that cover to be a cover for the topology in which E is a sheaf. This is declared as a generic tool use, as is the general algebraic-space definition.

Step 2 proves the comparison on an arbitrary scheme Z, not just on field-valued points. The same coproduct node gives the disjoint open partition pulled back from W; the open-factorization node gives the actual scheme maps b_i, not merely set-theoretic factorizations. The fibre-product node gives uniqueness on each piece, and the morphism-gluing node gives both existence and uniqueness of the global inverse. I wrote both inverse checks and the precomposition check; no preservation of arbitrary coproducts by Yoneda or unstated topos extensivity is assumed. The argument is one direct application of the four cited universal properties, so no additional comparison lemma is needed.

Step 3 applies clauses (1) and (2) of lem-weil-pbc-etale-composition-cancellation to the open immersion P_i to P and the etale P to T. The source-locality node explicitly covers arbitrary open coverings of the source, hence applies to the components of C even for infinite I. Surjectivity is a two-choice point lift through P and its inverse-image open covering, not an implicit base-change theorem. These are exactly the projection and hypotheses used in the scheme-test definition. I checked that no quasi-compactness, separation or Noetherian assumption has been introduced.

Step 4 uses the point-classes definition for common-field equivalence and the existing Mathlib-leaf lem-weil-pbc-morphism-from-spec-field for the canonical residue-field point and factorization of a field-valued point. Surjectivity over Spec K produces a point of the representing scheme, not a K-rational lift. Its residue field provides the required extension K to kappa(z), and factoring its image in W shows equality with the image of the actual scheme point y. This explicitly verifies the point-map conclusion even when no rational lift exists over K itself.

Step 5 uses the affine-open-basis node twice: at s(v) in S and at v inside s^{-1}(S_v) in V. The open-factorization node supplies the structural morphism through S_v. The only indexing is by the set of points of V within the given universe convention. No affine intersection theorem is used. I checked the empty atlas and empty indexing set: the test P is empty and its surjection to T forces T empty; the sectionwise inverse is empty gluing and etaleness follows from the same source-locality statement. The affine construction is the empty family when V is empty.

I also tested the identity atlas of a scheme, overlapping open covers, repeated cover members, infinite covers and arbitrary nonaffine test schemes. The partition used in step 2 is pulled back from the disjoint coproduct W, so overlapping U_i in V cause no false disjointness assertion about P_i inside P. Fields with nontrivial residue extensions are handled by step 4. All new-node requirements B1--B9 are vacuous because no nodes were added; B10, C1--C8, D1--D5 and E1--E6 were checked through the statements and arguments above. No SGA source, compiler, Lake command, repository write or launcher modification was used.
