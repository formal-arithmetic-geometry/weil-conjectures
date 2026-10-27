# Stage-1 report: lem-sfb-missing-fibre-finite-presentation-approximation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-missing-fibre-finite-presentation-approximation.json — statement, now split in seven steps; no Mathlib match. The statement and previous search records are retained.
- citations.json — 24 entries, one for every step/node citation, quoting the current node statements verbatim.
- searches.jsonl — five actual searches made through the prescribed msearch command, supplementing the historical searches in the item.
- report.md — this report. write_split.py is sandbox-only preparation material.

There are **0 new nodes and 0 new Mathlib leaves**. Existing Mathlib leaves are reused rather than duplicated. Every non-elementary input already has a DAG node.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, 05BD, missing-fibre terminology and finite-presentation approximation found no project declaration proving this statement. The general finite-presentation approximation API has other hypotheses and conclusions. The nearby proper-closed-fibre approximation node concerns a proper morphism and a closed subscheme of the base, not an arbitrary closed subscheme of X after base change.

## WANTED

None. The proof's source is locally available: literature/stacks-project/limits.tex, Tag 05BD, label lemma-separate, including its complete proof. Algebraic inputs are in algebra.tex (0BUF, 00D6, 00D7, 00DD, 00E6); schematic-image and affine-morphism inputs are in morphisms.tex (01R8, example-scheme-theoretic-image, 01S7, 01SC, 01SD, 01SH).

## Problems found and changes

No statement dispute. In particular, quasi-separatedness of X is unnecessary: no intersections of its affine opens are assumed affine or quasi-compact. The finite affine cover follows from quasi-compactness over the given affine base. The image morphism used in the last part is affine for an independent reason (base change of the affine-to-affine map V to Tprime, composed with a closed immersion).

I keep the pre-localization equations x_i + sum f_ij c_ij = g_i in the source proof instead of shrinking V to normalize them to 1. This is the same proof with that optional shrink omitted: after descent g_i remains outside the contracted prime, and therefore is a unit at the fibre under consideration. The report and proof explicitly give the denominator product and the additional annihilator needed for equality of fractions; no unsupported instruction to clear denominators remains.

The filtered index category is the existing small category built from a set of explicit finite polynomial quotients, not the large category of all algebras. The stage-algebra and index universes are enlarged together as required by the cited tensor-colimit statement. Both colimit nodes are declared generic off-unit tools in split_report.tool_uses. They implement precisely the algebraic operations in 05BD rather than changing the unit route.

The blueprint ancestor command returns None for this item's inherited chain. I retain the null ancestor and full inherited via list, as the command requests, and the already precise from.place. I read the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md: this is a supporting algebraic-geometric input far below its direct-image clause (3), not a change to that clause. Whole-blueprint searches for 05BD and missing fibre found no equivalent imported node. General finitely-presented and scheme-theoretic-image searches exposed only distinct descent/closure inputs, which were reused where applicable. same_as is therefore [].

## Not duplicates

No new nodes were created. In particular the small filtered algebra presentation, tensor-colimit element/zero tests, finite affine cover, fibre-ring localization formula and affine kernel formula already existed and were cited. The item is not a duplicate of lem-weil-pbc-proper-closed-fibre-approximation: that node requires properness and approximates an entire fixed closed fibre over a quotient of the base; this item assumes only quasi-compactness and approximates an arbitrary closed subscheme avoiding a selected point fibre.

## Mathlib searches

The exact queries and actual results are in searches.jsonl and appended to mathlib_searches without changing the historical entries. Both LeanFinder phrasings returned closed inverse-limit point existence, equality descent for morphisms, fibre compactness and related results. Loogle returned fpqc/fppf descent instances. LeanSearch returned empty-scheme affineness, closed immersion base-change stability, closed subscheme construction and descent properties. The prescribed grep found no 05BD/missing-fibre/finite-presentation separation statement. I read the candidate statements in Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean (closed inverse-limit points and locally finite-type morphism equality descent): they do not produce the closed subscheme and selected empty fibre required here. None is an exact match or one-line specialization. All services answered; none is recorded as unavailable.

## Review by Q53

I read Tag 05BD in limits.tex against every clause of the item: the arbitrary ring, quasi-compact f, arbitrary g, selected t, containing image, empty descended fibre, affine neighbourhood and finite-presentation output all agree. The finite polynomial presentation is supplied by the finitely presented algebra itself, not by a finite-type assumption on X. I read 0BUF's set-restriction footnote, 00D6/00D7's element/equality description, 00DD's tensor-colimit formula, 00E6's localization/quotient fibre diagram, and the 01R8 statement and affine example. There are no new nodes whose source needs a separate audit.

1. Step 1 uses def-pc-scheme for affine neighbourhoods, def-weil-finite-type-morphism specifically for its quasi-compactness definition, and lem-pqf-finite-affine-cover-qc-open with U=X. Unlike the qcqs cover alternative, this node imposes no quasi-separatedness. The affine-fibre-product statement gives exactly C_i tensor B and the projection maps; def-weil-closed-immersion gives the quotient D_i=R_i/I_i; def-pc-scheme-fibre and the same affine formula give its fibre. All schemes and ring maps are introduced before use.

2. Step 2 applies the fibre-ring node to B→D_i, not to the ring R_i with its ideal accidentally forgotten. Its statement gives the localization and its fraction equality as well as the quotient by q. Empty spectrum implies the zero ring using the basic-open/unit-ideal node with the empty family. Membership of 1 in qD_local gives a finite sum. Multiplying the displayed denominators gives s_i, and equality of fractions supplies h_i outside q; lifting back to R_i gives x_i in I_i. Thus the derived relation holds without any Noetherian or finite-generation assumption on I_i. This step is marked non-elementary and cites both inputs, not just definitions.

3. Step 3 uses exactly the statement of lem-weil-pbc-algebra-colimit-fp-algebras-over-it: a set of representatives of all finitely presented A-algebras gives a small filtered category with colimit B. The explicitly presented quotient set satisfies its hypotheses. This avoids an unjustified passage from a large filtered category to a small colimit.

4. Step 4 uses the tensor node's element-lifting clause with N=A and N=C_i. Tensor symmetry is written on simple tensors in both directions. The common-target axiom explicitly present in the algebra-presentation node combines the finite choices. q_lambda is an inverse image of q, so membership and nonmembership follow from the chosen images; no lifting of a prime or faithful-flatness argument is asserted.

5. Step 5 uses the tensor node's eventual-zero clause, not the injectivity of any structure map. Equations are imposed successively along arrows from the current stage, and its ring-map clause preserves all already imposed equations. Since the list is finite, this ends at a common stage. No general finite-equation descent lemma is hidden in this short finite iteration.

6. Step 6 checks the quasi-compactness hypothesis of the scheme-image node: a is between affine schemes; its base change p is affine by the two cited affine lemmas; the closed immersion is affine by the quotient characterization in its definition; composition is affine by its separate node; affine permanence gives quasi-compactness. The kernel formula in the cited image node states precisely the ideal equality needed, and the preimage of each target chart is Spec D_i because the projection to X is unchanged. In particular a lifted x_i maps to zero, so it lies in the image ideal. The factorization is supplied by the node's statement, not borrowed from its proof.

7. Step 7 uses the descended relation on the actual quotient fibre ring. The x term vanishes in J_i, the f terms vanish at q_lambda, and g is a unit since it is outside q_lambda. It follows that the fibre ring is zero. The charts cover the total scheme, so each empty chart fibre implies the whole fibre is empty. The image node supplies an actual scheme factorization, which is stronger than the set-theoretic containment requested. I do not infer scheme factorization from point-set containment.

I tested the vacuous cover X=empty, Z=empty, charts with zero coordinate/quotient ring, empty sums in the unit equation, noninjective presentation maps, and arbitrary non-quasi-separated X. All remain covered by the argument: an empty finite chart list imposes no equations and the filtered category is still nonempty; a zero D_i still allows g_i outside q; only finite data, never finite generation of the whole defining ideal, are descended. T has a point t, so the affine neighbourhood's ring has a prime and the chosen g_i never lies in it. Non-affine T is handled solely by restriction to the chosen V.

I checked delivery-errors B–E against the files: the statement is unchanged, no unsplit node contains a proof, no new duplicate or restatement is introduced, every uses entry has a verbatim citation entry, proof_deps is exactly their union, and no step exceeds 2000 characters (maximum 1139). No non-elementary step is marked elementary. All writes were confined to the sandbox, with no Lean or build invocation.

## Unfinished work

None in the stage-1 split. The server delivery dry run returned OK (not pushed), preflight passed, at 989b012beca. A local read-only consistency check also verified all 24 verbatim citation substrings and the exact union of 17 existing proof dependencies. This report update is followed by the final dry run and authorized direct push.
