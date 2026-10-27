## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-eventually-smooth.json: statement, now split in four steps; no Mathlib match. The imported statement, source, provenance, and four prior Mathlib-search records are retained. Six actual Q19 searches are appended.
- citations.json: verbatim supporting statement quotations for every step/node pair.
- No new nodes and no Mathlib leaves are created. report.md is this report; prepare.py is a sandbox-only preparation script, not a delivery file.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and eventual-smoothness/limit/descent terms found scheme and ring results, including AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_diagram and Scheme.exists_smooth_pullback_snd_of_isLimit. Their statements quantify over Scheme, and do not cover algebraic spaces. They cannot attach the item. The former is already attached to lem-sbc-affine-diagram-smooth-stage, which is used as a dependency.

## Wanted literature

None. All sources used are present under literature/stacks-project/.

## Errors and changes

No mathematical statement error found. The existing statement is the specialization of spaces-limits.tex Tag 0CN2 to the morphism to its affine base; finite presentation gives the quasi-compactness needed to choose the affine atlas. The source's final step cites scheme descent Tag 0C0C. Its affine part is already a DAG node, so there is no need to create another eventual-smoothness lemma.

The supplied blueprint ancestry has from.node = null, and tools/blueprint_refs.py ancestor prints None. I retained that ancestry instead of inventing a blueprint id. The most recent blueprint (latest, commit 7284bb09daf97437d544c51882b325f9c52cd345) was read at sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and the direct-images proof. This auxiliary algebraic-geometry lemma is below the recorded arithmetic approximation input, not itself a blueprint theorem. Searches for 0CN2, smooth stage and eventual smoothness returned no matching blueprint statements. The affine-etale search returned ind-etale/cohomological continuity statements, which do not state this result. No unit or chapter route was changed, and this item is not a unit key node.

The brief's old coord/dag-sync.md is not present; the explicit shared-read-only repository instructions were followed. No repository or launcher files were written, no git command was run by the worker, and no Lean/compiler/Lake/build command was run.

## Unfinished work

None in this one-level split. All proof inputs already exist. Their subsequent formalization or further splitting is outside this item.

## Not duplicates

No new-node pairs: zero new nodes. In particular, lem-sbc-affine-diagram-smooth-stage is reused for schemes rather than duplicated for the chart. The algebraic-space item is not a duplicate of that scheme-only statement.

## Review by Q19

I read the statement and full proof of spaces-limits.tex Tag 0CN2 (lemma-descend-smooth), as well as Situation 084W. The reduction chooses an affine atlas and applies scheme smoothness descent. I used the identity chart of the already affine base, which removes the second atlas from the source proof without changing the argument. I read spaces-properties.tex Tag 03H6 and its preceding quasi-compactness criterion, spaces-morphisms.tex Tag 03MJ and its smoothness section (03ZE/03ZF), and limits.tex Tag 0C0C. The split stops at the existing affine-model input rather than repeating its ring proof. There are no new-node sources to review.

Step 1 uses the actual statement of lem-trf-space-qc-finite-affine-atlas-refinement, including its last sentence giving one affine surjective etale chart for every quasi-compact algebraic space. The quasi-compactness hypothesis follows by testing the quasi-compact morphism on its affine base itself. No quasi-compactness or separation of an arbitrary atlas is assumed. I checked the statement of lem-sfb-scheme-etale-source-target-properties: local finite presentation is explicitly one of its five properties. The statement of lem-sfb-space-etale-presentation-property-criterion then says every presentation has that property. Thus the map U_0 to T_i0 has the exact hypothesis needed for affine-model descent. No lfp composition theorem is hidden in this step.

Step 2 uses the base-change clause of lem-trf-space-fibre-products-etale-covers, whose statement explicitly preserves joint surjectivity and etaleness. The equality of the two descriptions of the source is the fibre-product universal property, not a claim about factoring through an image. The same two presentation/locality statements apply to smoothness and identify smoothness of the chart map over T. All sources U_i and U are schemes by representability of the atlas; the base T is a scheme by hypothesis.

Step 3 reads lem-sbc-affine-diagram-smooth-stage literally: it takes a small cofiltered affine diagram, affine P and Q, compatible maps to Q, an lfp P-to-Q map, and a smooth limit pullback. The directed tail is nonempty (contains i0), small (a subset of I), and its opposite is cofiltered. The argument explicitly extends a tail cone to the original diagram via common upper bounds, verifying the same limiting cone. P=U_0 and Q=T_i0 are affine, h_0 is lfp from step 1, and the smooth pullback is h from step 2. No surjectivity of base transitions, faithful flatness, or Noetherianity is inserted. The cited affine theorem supplies precisely one later smooth chart, not the full algebraic-space conclusion.

Step 4 uses only clause (2) of lem-pc-proper-base-change; its statement explicitly gives smoothness under arbitrary scheme base change. The step spells out the fibre-product identification, so it does not rely on an unexplained transport. The two presentation/locality statements then give smoothness of X_i over T_i from the single surjective etale chart already obtained in step 2. This proves every later stage rather than merely the existence of one smooth stage. Quasi-separatedness is allowed but no stronger separatedness is used.

I checked delivery-errors B through E against the written files. There are no unsplit new nodes carrying proofs, no relocated clauses of the item, and no unrecorded semantic searches. Every cited node was opened and read at the statement level; citations.json was verified against those exact statements. I also checked the six proof dependencies' full statement/proof dependency closures, and none reaches this item. Four off-unit generic tools are declared in split_report.tool_uses; the other two proof inputs belong to the item's unit. The split does not use a definition as a permanence theorem. Every step has fewer than 2000 characters (475, 626, 705, 669); none hides a separate comparison lemma.

Edge cases checked: the empty algebraic space has the empty affine atlas Spec(0) permitted by the atlas theorem, so the argument remains valid. A singleton index set just returns its sole stage. A directed poset need not have a least element: the tail argument needs only the chosen i0 and common upper bounds. Base transitions can have empty images and need not be surjective; all persistence is by arbitrary base change. No non-affine source is accidentally passed to the affine-model input.

The Mathlib hits were read: LocalFlatDescent.lean lines 41-42 is fpqc descent for scheme morphisms and has a different diagram and hypotheses. Smooth.lean lines 117-126 supplies scheme smoothness base-change stability (the search service also returns obsolete IsSmooth spellings); it does not supply descent for algebraic spaces along an inverse limit. The other semantic hits are smoothness definitions, standard smooth charts, lfp consequences, or ring properties. Both Loogle queries returned zero hits. A second semantic phrasing still returned only scheme chart/base-change material. The inherited searches were preserved, and all appended queries match searches.jsonl exactly.
