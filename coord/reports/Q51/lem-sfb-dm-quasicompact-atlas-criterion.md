# Q51 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dm-quasicompact-atlas-criterion.json — statement, split; Mathlib searches give no match for the stack criterion.
- citations.json — verbatim statement excerpts for all citations in the five proof steps.
- report.md — this report. No new nodes and no new Mathlib leaves.

## Attachments

None. Searched the live lean/WeilConjectures source for the exact blueprint tag and atlas/quasi-compact terminology and for AlgebraicStack/DeligneMumford. No complete declaration of this item was found; no upstream sorry declaration is treated as finished evidence.

## Wanted literature

None.

## Findings and corrections

The imported statement agrees with Stacks 04YC, conditions (1), (2), (3), (5), restricted to Deligne--Mumford stacks. Kept its entire statement, including the arbitrary base, point-surjectivity convention, empty case, and lack of separatedness assumptions. The seeded node had no proof. Its old searches were preserved and four actual msearch.py searches were added. LeanFinder and LeanSearch return scheme compactness/morphism results, not the stack equivalence; Loogle and whole-Mathlib grep have no AlgebraicStack/DeligneMumford matches. A second semantic phrasing concerns surjective quasi-compact stack sources, rather than just affine atlases. None is a one-line specialization proving this item.

The inherited creation chain has no machine-resolvable blueprint ancestor (the ancestor command reports None). Retained its null from.node and via list and its explicit textual anchor; read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof, paragraph (3), as well as the DAG chapter and unit. This proof supplies the generic atlas prerequisite below the existing alteration/moduli and finite-type-calculus route. Whole-blueprint searches for quasi-compact stack, quasi-compact Deligne, affine smooth, smooth surjective, and disjoint union of affine found no equivalent blueprint item. Searches of the whole DAG found the exact scheme coproduct lemma and topology lemmas, so no replacement or duplicate nodes were created. No unit record changed because this item is not the unit's key statement.

## Unfinished work

None in the authorized one-level split. Existing unsplit inputs remain their own items.

## Not duplicates

No new nodes. Reused lem-weil-pbc-finite-affine-coproduct-spectrum instead of introducing a finite-disjoint-affines lemma, and lem-sfb-stack-point-topology-flat-lfp-open for stack continuity and open images. The finite-type-over-a-field affine-atlas node has additional hypotheses and was not used to infer this arbitrary-base criterion.

## Review by Q51

I read the complete statement and proof of Stacks 04YC in stacks-properties.tex (lemma-quasi-compact-stack), and the statement and atlas comparison argument of 04XL (lemma-topology-points). I also read schemes.tex 01I5 (lemma-disjoint-union-affines), 01IT (lemma-basis-affine-opens), morphisms.tex lemma-open-immersion-etale and lemma-composition-etale, algebra.tex 00E8 (lemma-quasi-compact), and Mathlib's sigmaSpec definition, coprojection identity and finite IsIso instance at Limits.lean:607, 611 and 641. There are no new nodes requiring independent source checks.

For step 1 I opened and read the current statements of def-sfb-stable-pointed-moduli-groupoids, lem-pc-fppf-affine-open-cover, lem-weil-pbc-open-immersion-etale, lem-sfb-stack-chartwise-smooth-etale-calculus, lem-sfb-stack-point-topology-flat-lfp-open, and def-trf-scheme-algebraic-space. They give respectively the etale atlas, affine cover, etaleness of each inclusion, composition and etale-implies-smooth/flat/lfp, the open-map theorem for a flat lfp algebraic-space source, and the scheme-to-algebraic-space embedding. All source hypotheses hold: the chosen affine opens are schemes; the maps are representable etale before the open-map theorem is applied. The chart calculus explicitly states the equivalence between its scheme-chart surjectivity test and field-extension local lifting. This gives surjectivity on point classes. The smooth-atlas topology and the item's etale-atlas topology agree by testing inverse images along this same atlas. Thus no assumption about open images is smuggled out of a topology definition.

For step 2 I read the complete statements of lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-finite-affine-coproduct-spectrum, and reread the coproduct clause of the chart calculus. The former supplies a scheme with open disjoint component images; the latter identifies its finite affine coproduct with the product-ring spectrum. The calculus explicitly glues a set-indexed family of etale scheme-source maps to a representable etale stack map, so no scheme-only smooth-coproduct theorem is applied to a stack target. The family here is finite and has the stipulated universe size. Surjectivity follows directly from the chosen images covering the point set. The resulting S-map is obtained from the component S-maps. I checked the empty family separately: its product ring is the zero ring, and its spectrum and source are empty. The point-surjectivity convention then gives exactly the desired empty case.

For step 3 I read lem-weil-pbc-affine-scheme-qcqs: its statement includes the compactness of the affine source, with no field or finiteness hypothesis. Only that compactness clause is used; no quasi-separatedness of the original stack is inferred.

For step 4 I read def-pc-fibre-product, the stack and atlas conventions in def-sfb-stable-pointed-moduli-groupoids, the identity/open-immersion instance of lem-weil-pbc-open-immersion-etale, def-trf-scheme-algebraic-space, and the scheme-topology clause of lem-sfb-stack-topology-open-substacks. I corrected an initial citation to def-trf-algebraic-space: its definition alone would not prove that a representable presheaf is a sheaf. The existing scheme-as-algebraic-space node explicitly supplies that property. For its discrete fibred groupoid, effectiveness of etale descent is just the sheaf gluing axiom, written out in the step. Fibre products give the representable diagonal, the identity gives the atlas, and its point topology is the usual one. This is the elementary interpretation of the given scheme as a DM stack, not a new stack-existence lemma.

For step 5 I reread the continuity clause of lem-sfb-stack-point-topology-flat-lfp-open. It applies to every stack morphism, without representability, flatness, or finite presentation. Thus it applies to the arbitrary morphism in (4). The finite-subcover argument is written explicitly, using precisely point-surjectivity and compactness of the source. No Hausdorff condition is used.

I checked delivery-errors B through E against the actual files: the statement introduces its objects, all cited facts occur in cited statements, all non-elementary inputs have nodes, and there are no new clause-restatements. Every uses entry has a verbatim quote in citations.json. All five steps are shorter than 2000 characters. Small cases checked were the empty stack, an affine scheme with identity atlas, a non-quasi-compact scheme (the finite selection cannot be made), and a finite-group classifying stack (field-extension lifting is allowed, rather than incorrectly requiring lifts over the original field). No finite-type, field-base or separation hypothesis entered the argument. No SGA source, Lean write, compilation or build was used. The preliminary remote review_split check passed; the complete deliver.py preflight is the final validation.
