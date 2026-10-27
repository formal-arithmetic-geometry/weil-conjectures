## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-noetherian-coherent-acc.json` (statement, split; seven proof steps; no Mathlib match for the whole algebraic-space statement), and the required `citations.json` and this report. Searches are logged in `searches.jsonl`. No Lean, compiler, build, repository file or launcher file was written or run. The initial sandbox contained only dispatcher markers, not an earlier split; the item was copied from the read-only current repository.

## New nodes

None. In particular no separate nodes were made for the item's three clauses or for the elementary descent-of-equality and maximal-member arguments. There are zero new Mathlib leaves.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, `AlgebraicSpace`, coherent/Noetherian and ascending-chain language found scheme declarations, notably `NoetherianQuasicoherentSubmodules.lean`, but no project declaration giving the algebraic-space statement. A scheme theorem does not attach this item. No declaration was asserted closed merely because its statement or docstring exists.

## WANTED

None. The needed Stacks sources are present.

## What changed and what was wrong

The imported statement is unchanged and agrees with Stacks. Its proof and proof-dependency lists were empty. The statement's references to the scheme definitions of locally Noetherian and coherent are read with the explicit chart conventions already stated in the item, not as assertions that an algebraic space is a scheme. The proof now separately supplies local Noetherianity, quasi-compactness, and quasi-separatedness, then all three coherent-finiteness conditions, ACC, and the maximal-member consequence. The proof does not use Noetherianity or quasi-compactness of an arbitrary chart. The affine atlas in the ACC step is what supplies a single global stabilization index.

The item's existing blueprint ancestry ends at a null ancestor, as `blueprint_refs.py ancestor` confirms; its precise existing `from.place` and `via` list are preserved. The current blueprint is `literature/blueprint/latest/`, where the unit's files lie under `sec-six-functors-basics/sk-thm-sf-ctf-stability/`; the unit record's historical source path under `sec-six-functors/` is not the current file path. I read the current unit statement and its proof, including the proper/open direct-image and compactification paragraph. The present supporting Stacks argument remains on that inherited direct-image prerequisite chain and does not alter the chapter or unit route.

Nothing mathematical remains unfinished in this one-level split. The reused scheme and chart prerequisites retain their own current statuses.

## Searches and reuse

I searched the whole DAG for the source tags 07UB, 07UJ and 04ZK and inspected matching coherent-module and Noetherian candidates. I also searched node titles/concepts for affine atlases, finite presentations, local Noetherian inheritance, quasi-compactness and quasi-separatedness. I opened the statement of every cited node, including the scheme finite-presentation affine criterion and the exact etale/Zariski finiteness comparison; the latter is stronger than a bare equivalence of quasi-coherent categories and is explicitly cited where ambient submodules and finite presentations are used.

Whole-blueprint searches using `tools/blueprint_refs.py search` for `Noetherian coherent`, `ascending`, `coherent` and `Noetherian` found no blueprint node stating this whole algebraic-space assertion. Scheme nodes `pqf-lem-locnoeth-lft` and `pqf-lem-coherent-ft-locnoeth` were reused. The exact atlas node is `lem-sfb-qc-space-affine-etale-atlas`; the finite-scheme-cover node requires separation and a field and was therefore not used. The general quasi-coherent groupoid equivalence is unnecessary: restriction plus the scheme comparison suffices.

All new Mathlib searches used the required msearch command. LeanFinder was tried with two different phrasings; LeanSearch, Loogle and grep were also used, and their exact queries and actual outcomes are recorded in the item and tool log. The hits are scheme local-Noetherian theorems, general sheaf presentation data and Noetherian algebraic-module results. I read `Mathlib/AlgebraicGeometry/Noetherian.lean` at 239–242 and the sheaf presentation definitions in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`: they do not prove coherent algebraic-space ACC. The pre-existing search records were preserved rather than claimed as new searches by Q43.

## Not duplicates

No new nodes. The whole assertion is not a duplicate of the scheme ACC node: the latter has a scheme, not an algebraic space, as its hypothesis. It is cited for the affine scheme atlas only.

## Tool uses

The off-unit scheme inheritance, etale descent, etale composition, affine Noetherian rings, affine module presentations, finite-module finite presentation, scheme coherence, scheme ACC, and scheme etale/Zariski equivalence are generic prerequisites. Their uses are declared in `split_report.tool_uses` when they are neither definition nodes nor Mathlib leaves. They supply the chart reduction of the Stacks proof, not a substitute for any unit-level direct-image theorem. No top-level `tool_uses` approval was added.

## Review by Q43

I read `spaces-morphisms.tex`, Tag 04ZK, `lemma-locally-finite-type-locally-noetherian`; `spaces-cohomology.tex`, Tag 07UB, `lemma-coherent-Noetherian`, and Tag 07UJ, `lemma-acc-coherent`; `spaces-properties.tex`, Tag 03H6, `lemma-quasi-compact-affine-cover`; and the scheme reductions in `coherent.tex`, Tag 01XZ, `lemma-coherent-Noetherian`, and Tag 01Y8, `lemma-acc-coherent`. I checked the tags against `literature/stacks-project/tags/tags`. There are no new nodes whose statements need independent source verification. The item assumes exactly the hypotheses needed: a scheme base S; finite type and quasi-separatedness for inheritance of global Noetherianity; locally Noetherian for the equivalence; and global Noetherianity for ACC.

For step 1 I checked `def-trf-algebraic-space` and `lem-trf-space-fibre-products-etale-covers`: they supply the atlas, the scheme-valued base change W and its surjective etale projection to T. `lem-weil-pbc-etale-composition-cancellation` is a scheme statement, so the text applies it only after scheme base change to verify the composite etale map. The finite-type definition applies to the compatible chart map W to V. `pqf-lem-locnoeth-lft` has exactly the locally finite type and locally Noetherian target hypotheses in force. `lem-trf-etale-local-noetherian-descent` applies to W to T without a finite-type or quasi-compactness assumption on T. Thus every chart of X is locally Noetherian, not just a specially chosen chart.

For step 2 I checked that `lem-sfb-qc-space-affine-etale-atlas` assumes only quasi-compactness, not separation, and gives an affine surjective etale atlas. `lem-sfb-space-quasicompact-affine-tests` supplies exactly the quasi-compactness of X times_B V, as V is affine. Applying the same atlas lemma again gives U. The cover base-change and scheme composition statements justify the successive etale covers and their surjectivity, and the atlas characterization gives quasi-compactness of X. `lem-sfb-space-quasiseparated-test-calculus` explicitly states composition of quasi-separated maps, so it applies to X to B to Spec Z. I have not silently inferred quasi-separatedness from local Noetherianity for algebraic spaces.

For step 3 I checked the local-presentation definition of quasi-coherence, the canonical scheme etale/Zariski equivalence and the exact finiteness comparison, whose statement explicitly reflects finite type on both sites. `pqf-lem-coherent-ft-locnoeth` asserts coherence iff quasi-coherent finite type for a locally Noetherian scheme. These are precisely the chart modules here. The passage to the covering condition is unpacking the local finite generating epimorphisms, not a separate coherence theorem. The structure sheaf is locally free of rank one even in the zero-ring case.

Step 4 is elementary: a finite local presentation is an allowed arbitrary local presentation, and its epimorphism from finite free generators is finite type. It is not being used as a non-elementary noetherian criterion.

For step 5 I checked the actual statements, not just the titles: `pqf-lem-affine-open-locnoeth` gives the Noetherian ring of any affine chart-open; `lem-weil-pbc-quasi-coherent-finite-type-affine` gives finite sections in clause (a) and the converse affine finite-presentation criterion in clause (b); `lem-sc-noetherian-finite-module-finite-presentation` applies to that finite module. The exact finiteness comparison explicitly carries finite presentation back to the etale site. The final local gluing is just the definition of having a finite presentation locally. I did not cite the two-condition scheme coherence node as though its statement included a finite-presentation clause.

For step 6 I checked that the affine atlas U is locally Noetherian by the item convention and quasi-compact by affineness, hence a Noetherian scheme. Its module is coherent by the definition in the item, not by an unquoted strengthening of a quasi-coherent equivalence. `lem-sfb-scheme-etale-module-exact-finiteness-comparison` says the equivalence is exact in the ambient sheaf category, so the inclusions become actual scheme submodules. `lem-weil-pbc-noetherian-acc-quasi-coherent` then gives exactly a single eventual stabilization index on U. Etale pullback is restriction to localized sites, as `def-trf-algebraic-space` states. The text proves the remaining equality on X by lifting each section to F_n over T times_X U and gluing it; the monomorphism into F guarantees agreement on overlaps. This proves equality of subobjects, rather than merely isomorphism of abstract modules.

Step 7 uses only the ACC just proved, coherence of the rank-one structure sheaf from step 3, and classical recursive choice in the fixed universe. No new non-elementary order-theoretic lemma is hidden in it.

I checked B1–B9 and C1–C8 against the files: no new statement-only placeholders or duplicate nodes, self-contained unchanged item, all source tags verified, single TeX escaping, searches actually run, and all cited statements copied verbatim into citations.json. D1–D5 are addressed by the written chart and gluing arguments; none of the clauses was moved to a newly named black box. For E I tested the empty space, the zero module, zero-rank presentations and constant chains. I also checked why quasi-compactness cannot be dropped from ACC: on an infinite disjoint union of fields the quasi-coherent ideals supported on the first n components form a nonstationary increasing chain, so the proof must use a single affine atlas only in the globally Noetherian case. Every step is shorter than 2000 characters; there is no long-step hidden subclaim. During this reading I corrected the scheme ACC tag from an initial mistaken 01Y1 to the actual 01Y8 before delivery. I also corrected the parenthetical file reference for Tag 08BE to `spaces-more-morphisms.tex`, verified against the tag table and its maximal-ideal paragraph. No statement correction was necessary.

## Validation

Server `review_split` passed with zero new nodes. The first required `deliver.py --no-push` completed successfully with preflight passed. After checking and correcting the parenthetical source filename for Tag 08BE, the final dry run is repeated on the final files before pushing.
