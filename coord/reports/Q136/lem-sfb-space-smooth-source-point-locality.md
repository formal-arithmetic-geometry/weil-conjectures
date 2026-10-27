# Q136 stage-1 delivery: lem-sfb-space-smooth-source-point-locality

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-smooth-source-point-locality.json`: statement node, split; original statement and statement dependencies unchanged. Five proof steps; no new nodes and no Mathlib leaves. Existing Mathlib searches retained and the actual sandbox search log appended with its real queries and results.
- `citations.json`: 17 step/node citations, each copied verbatim from the existing cited statement. Some quotes include the whole statement because the step uses several of its clauses.
- `report.md`: this report. All writes are in the assigned sandbox. No Lean, compiler, Lake, direct repository git command, launcher modification, or agent delegation.

## Attachments

None for the item. Searches by the exact blueprint tag and smooth-source/point-locality concepts under `lean/WeilConjectures/` found no project declaration stating the algebraic-space item. The existing scheme theorem `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective` already belongs to `lem-sbc-smooth-flat-surjective-source-descent`; I read its statement and proof in `lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` (currently lines 697 onward) and cite its existing node rather than creating another.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`. The inherited brief's `coord/dag-sync.md` is absent, but this direct-delivery brief supplies the current live source paths and delivery commands. No missing mathematical document is involved.

## Findings and changes

The imported statement is correct, including the absence of a local-finite-presentation hypothesis on h and the absence of surjectivity of q. Its empty proof was filled. I read Stacks `spaces-descent.tex`, Tag 06F2 (`lemma-smooth-smooth-local-source`), its definition of source locality, and the complete transfer proof Tag 06ER (`lemma-transfer-from-schemes`). For the pointwise reduction I read `spaces-morphisms.tex`, Tags 03ZD, 03ZE, 04TA, 04AJ, and 042S, and `spaces-properties.tex`, Tags 03BZ and 03IE. Scheme descent is `descent.tex`, Tag 05B5 (`lemma-smooth-permanence`); Tag 036U and the preceding Tag 02KM give the smooth-cover version as well. I also read the scheme open-immersion lemma 02GP and the presentation criterion 03MJ.

A tempting citation would be `lem-sfb-space-fppf-source-locality-transfer`. Its hypotheses do not apply to smoothness: smoothness is not fppf-local on the source in the two-sided sense that would preserve it under arbitrary fppf precomposition. For example Spec(k[epsilon]/epsilon^2) to Spec(k) is fppf and not smooth, whereas the identity of Spec(k) is smooth. Instead, steps 3 and 4 explicitly carry out the scheme-chart argument of 06ER for the single smooth surjection r. This uses the existing scheme source-descent theorem 05B5, without assuming the desired algebraic-space conclusion as a black box.

The chapter and unit records were read, as were SETUP's three levels. The current latest blueprint proof `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), is the inherited alteration/moduli prerequisite route. This small smooth-locality input changes none of that route. `blueprint_refs.py ancestor` returns None; the inherited null ancestor and explicit place/via chain are retained. Searches of the whole imported blueprint for smooth source, smooth local, smooth surjective, smoothness, 036U, 05B5 and 06ER found no blueprint node stating the item. The generic off-unit tools are explicitly declared in `split_report.tool_uses`.

The five original sandbox searches and their saved results were read and reused. Additional msearch queries checked scheme source descent and alternative phrasings; composition, formal lifting, smooth loci and target-base-change descent results do not state this algebraic-space pointwise result. The existing scheme source-descent node was found before any new node was created. No search service failure was treated as mathematical absence. No new node was needed, so there is no new-node search requirement left open.

## Not duplicates

No new nodes. In particular, no duplicate of `lem-sbc-smooth-flat-surjective-source-descent`, `lem-sfb-space-fppf-source-locality-transfer`, `lem-sfb-space-etale-presentation-property-criterion`, or the existing open-subspace and smoothness-calculus nodes was made. The fppf transfer node has different hypotheses and was not used. The existing etale-source smoothness node is for schemes and etale source maps; it does not state the present smooth-source result for algebraic spaces.

## Review by Q136

I checked the item against the Stacks sources just listed, with each cited node's statement open. There are no new-node statements to audit. The argument keeps q smooth and h arbitrary throughout: any flatness or local finite presentation used belongs to q restricted to W, or to the scheme cover p, never to h or to its chart d in advance.

Step 1 uses precisely clause (1) of the scheme etale-composition node: an open immersion is etale. The fibred-groupoid calculus states that representable etale maps are smooth and that smoothness is stable under composition and base change, also for maps of algebraic spaces. Applied on scheme tests, these clauses make open subspace inclusions smooth. The open-factor/scheme-test node states both the open pullback and its inverse-image point set. Thus Z_A really is an open neighbourhood of z, and the composite on it is smooth. Viewing a sheaf of sets as a discrete algebraic stack introduces no new geometric hypothesis: descent is the sheaf condition and its etale atlas is smooth.

Step 2 uses the same smoothness calculus to restrict q. The stack chartwise calculus expressly says smooth morphisms are flat and locally of finite presentation; it applies to spaces viewed as discrete stacks. The universally-open node says a flat lfp space map has open image. The etale-open-image node's first assertion is the unrestricted bijection between open subsets and open subspaces; only that clause is taken, so q_W is not mistakenly assumed etale. The open-factor node expressly gives W times_X O isomorphic to W and the unique factorization. This identifies r with an actual base change, so the smoothness claim is justified; its point-surjectivity follows from the definition of O.

Step 3 uses the algebraic-space definition for etale scheme atlases and the fibre-product/etale-cover node for existence and covering base change. The fibred-groupoid calculus explicitly covers arbitrary base change, composition, etale implies smooth, and preservation of point-surjectivity. These show that a and c are etale and p is smooth and surjective. The scheme-presentation criterion includes agreement with scheme smoothness when both objects are schemes. Its hypothesis that smoothness is etale local on source-and-target is supplied by the scheme source-target-properties node, not taken from a definition or from a proof hidden in another node. All choices are a finite list of scheme atlases in the given universes, not an improper class-indexed cover.

Step 4 uses that same scheme property and the all-presentation clause of the criterion to get smoothness of dp from smoothness of gr. The chartwise calculus supplies flatness and local finite presentation of p. The exact statement of `lem-sbc-smooth-flat-surjective-source-descent` requires these two properties and point-surjectivity of p, all established; it assumes only smoothness of dp and concludes smoothness of d. It does not assume d lfp, separated, quasi-compact, or Noetherian. Finally the one-surjective-presentation clause of the criterion gives smoothness of g. This is the three-equivalence argument of 06ER written out on the actual charts rather than a citation to a transfer node with the wrong topology.

Step 5 is the definition of smooth at a point: q(z) belongs to the open point image O and h restricted to O is smooth. It adds no geometric lemma. I tested Z empty (vacuous), q an identity (the same locus), q a proper open immersion with image omitting the nonsmooth part of h (only its open image is used), a disjoint source component (no global surjectivity was inferred), and empty scheme charts (covered by the scheme source-descent statement). A ramified/non-smooth q is outside the hypotheses; no argument uses pointwise composition cancellation for such maps.

Against delivery-errors B-E: all objects were already introduced in the unchanged self-contained statement; the source locations have Stacks tags and labels; there is no new statement-only node with a hidden proof, duplicate, hollow data, or item-clause relabelling; each non-elementary step cites the actual statements it needs; proof_deps is their exact union; citations quote those statements verbatim; no forbidden SGA source is used. The longest step is 1037 characters, so no step exceeds 2000 characters or leaves a long unidentified comparison. The chart maps and the base changes are displayed explicitly to avoid an unproved 'transport' claim. The server dry run remains the authoritative check of the global graph and delivery fields.

## Unfinished work

None in this stage-1 split. The item is not claimed to be formally proved in Lean. Delivery checks and push are run with the prescribed delivery command after this report.
