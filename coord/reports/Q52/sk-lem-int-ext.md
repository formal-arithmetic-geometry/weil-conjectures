# Stage-1 report: sk-lem-int-ext

## Files written

- `dag/nodes/sec-six-functors-basics/sk-lem-int-ext.json`: item split in three source-backed steps; no new nodes and no Mathlib leaves.
- `dag/units/sk-lem-int-ext.json`: key-unit realization fields updated to point to the item and its three existing detail nodes.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `sk-lem-int-ext`, the exact blueprint tag, and the Ext/filtered-colimit/boundedness terminology. No sorry-free project declaration states this item exactly. No upstream sorry declaration was treated as an attachment.

## WANTED:

None. The current blueprint proof and all cited DAG detail nodes are available locally; no external source was needed beyond the Stacks tags already recorded by the detail node.

## What was wrong in the node, the blueprint, or the brief

The imported item had seven paragraphs, but its first formula, continuity argument, and boundedness argument were already represented by the existing same-unit detail nodes `det-lem-int-ext-formula`, `det-lem-int-ext-continuity`, and `det-lem-int-ext-bound`. The imported proof also left two substantial paragraphs uncited (`uses: []`) and marked one field `elementary: null`, which violates the stage-1 proof schema. I replaced that prose by three steps that cite the exact detail statements and preserve the item statement unchanged. Whole-DAG and whole-blueprint searches found no additional node stating the item or a missing strict sublemma, so no new node was created.

The item itself is not a Mathlib theorem. I ran the required LeanFinder, Loogle, grep, and LeanSearch queries through `msearch.py`; the hits were generic condensed, filtered-colimit, or homological-complex infrastructure and did not state the pro-étale constructible Ext result. The queries and verdicts are recorded in the item's `mathlib_searches` field and in the tool log.

## Review by Q52

I read the item, its unit and chapter records, the current main-20261015 section and proof, and the full statements of all three cited detail nodes. The source route is exactly the imported proof: reduce by finite stratification to `a_!L`, use the derived Hom formula, prove continuity on each stratum, and prove the uniform bound on each stratum before taking the finite maximum. The item statement has two clauses and no hypotheses were added or removed.

Step 1 cites `det-lem-int-ext-formula`. Its statement explicitly supplies both facts used: every bounded constructible complex has a finite filtration by shifted stratum pieces, and the stratum derived-Hom formula with the dual's Tor amplitude and colimit/limit behavior. The finite-filtration assembly via long exact Hom sequences is the direct devissage described by the source. I checked that the step does not use the proof of that node or any unstated construction.

Step 2 cites `det-lem-int-ext-continuity`. Its statement says verbatim that for every bounded constructible integral complex and every degree, Hom commutes with filtered colimits of complexes with a common lower bound. This is exactly clause (1), and the finite filtration from step 1 is the source's assembly argument. The common-lower-bound hypothesis is retained explicitly.

Step 3 cites `det-lem-int-ext-bound`. Its statement gives the explicit stratum bound and, consequently, an integer `d_C` for every constructible `C`, with vanishing for all `q>d_C` and all constructible `N`. This is exactly clause (2). The finite maximum is the final devissage in the source, and no stronger conclusion is inferred.

I checked small edge cases in the statements: the zero complex has an empty filtration and is covered by both clauses; a one-stratum object uses the stated bound directly; a degree-zero constructible sheaf is covered by the degree-zero filtration clause; and the filtered-colimit statement allows an arbitrary common lower bound. The detail nodes' hypotheses match the item coefficient `\\mathcal O_E` and the same pro-étale derived category. I also checked that none of the cited nodes depends on `sk-lem-int-ext`, so the new proof dependency graph has no cycle.

Against delivery-errors B–E, all cited ids exist and their quotes are verbatim in `citations.json`; every non-elementary step has a citation; no clause was relabelled as a new node; the statement is unchanged; and the only modified unit fields are the permitted `realized` and `realized_by` fields for this key unit. The existing detail nodes are reused rather than duplicated. No SGA source or prohibited route is involved.

## Not duplicates

None: no new node was created. The three cited detail nodes are intentionally narrower constituents of this item, with the formula, continuity, and boundedness claims separated; they do not duplicate the item's two-clause statement.

## What I could not finish

Nothing remains for this one-level split. The cited detail nodes remain existing queue items and were not edited. I did not write Lean or run any compiler, Lake, build, or global checks.


## Second reading by Q52

I independently opened the item, all three detail-node JSON files and their main-20261015 statement/proof files, the unit and chapter, the coefficient-setting and constructibility definitions, and the Stacks passages below. The item's two clauses are verbatim those of its current `_section.md`: integral coefficients, every bounded constructible C in (1), a common lower bound on the filtered diagram, and in (2) constructible sheaves C,N with an integer depending only on C. The source's standing coefficient/scheme conventions are retained. No statement correction was necessary.

- Original step 1 versus `det-lem-int-ext-formula` clauses (1),(2): the finite filtration and formula are stated there, but the reduction is redundant once the two existing general-C conclusions are cited. Removed this step and its formula citation. The formula still realizes unit paragraph 1 through the existing detail nodes and the unchanged unit realization.
- Original step 2 / final step 1 versus the complete statement of `det-lem-int-ext-continuity` and its source `sk-lem-int-ext-continuity.md`: PASS after making the direct application to arbitrary C,q explicit. The cited statement already includes devissage; the step now writes the precise canonical colimit comparison and retains the common lower bound. No fact is borrowed from the dependency's proof.
- Original step 3 / final step 2 versus the final sentence of `det-lem-int-ext-bound` and its source `sk-lem-int-ext-bound.md`: PASS after directly choosing its d_C. The old wording attributed the finite-maximum construction to the statement; that construction is in its proof. The final step uses only its stated general-C existence conclusion, with all N and all q>d_C.
- New nodes: NONE; zero new statement nodes and zero Mathlib leaves. B1–B7 introduce no new-node obligations. Both clause statements were already imported blueprint nodes, not newly introduced restatements. The formula, continuity and bound detail nodes remain unedited.
- Definition dependencies: checked `sk-def-sf-setting` introduces the coefficient extension, valuation ring and integral conventions, and `sk-def-sfb-constructible` actually defines Cons and Dbc. Added these two existing statement dependencies in place of the empty list. Traversal of their statement/proof closures, and those of both proof dependencies, reaches no `sk-lem-int-ext`, so these edges create no cycle through the item.
- Edge cases: C=0 makes every Hom/Ext group zero, with any d_C; on the empty scheme both conclusions are immediate. For one stratum and a free coefficient module the formula is derived sections. For the torsion local model O_E/pi_E, the resolution [O_E --pi_E--> O_E] in degrees -1,0 has derived dual in degrees 0,1, so Ext^1 is allowed and high-degree vanishing does not assert projectivity. For a shifted piece M[r], Hom(M[r],K[q])=Hom(M,K[q-r]), which is covered since continuity holds for every integer degree. In the boundedness clause C is a sheaf, so the finite degree-zero filtration requires no shift corrections. The indices n=1 and the torsion model introduce no exception; n=0 is not used by the positive-power reduction tower.
- Notation/source check: I initially suspected the formula's cHom was ordinary internal Hom, which would be false for the torsion local model; the current blueprint explicitly uses cHom as the derived tensor right adjoint (`sk-thm-sf-ctf-stability`, displayed adjunction), and `sk-lem-int-integral-heart`'s proof computes the derived dual above. This resolves that concern; there is no established source error to report. Stacks 099Q is `proetale.tex`, `proposition-enough-weakly-contractibles` (Noetherian constant coefficients, enough weakly contractibles; clause (5) is the cohomology/completeness assertion). Stacks 09AA is `proetale.tex`, `lemma-closed-immersion` (inverse image commutes with limits for a closed immersion). Stacks 08TB is `derived.tex`, `section-derived-limit` (the derived-limit triangle and following Milnor exact sequence). These passages concern the existing detail proofs; the final item steps do not pretend those tags themselves state either clause or a general sheaf-product bound.
- Searches: repeated independent queries through msearch.py, recorded verbatim in searches.jsonl and the item: LeanFinder “Hom from a perfect sheaf complex preserves filtered colimits uniformly bounded below” returned eight generic complex/truncation results; valid Loogle `CategoryTheory.Abelian.Ext` returned generic Ext declarations (read `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`); grep for Ext/constructible/PreservesFilteredColimits returned zero hits. None states this theorem. The original Loogle query was rejected for unknown identifier Hom, so corrected its verdict to rejected, not evidence of absence. Searches of the DAG and current blueprint reuse the existing integral detail nodes; the current `sk-lem-constructible-ext-continuity` permits rational coefficients and integral sources generated by finite locally free stratum pieces, so it does not state the unrestricted torsion-inclusive integral item; `sk-lem-uniform-constructible-ext` is the rational-coefficient bound. My source-tree search for the item id, Ext/constructibility and colimit terminology found no exact closed attachment; upstream master was only read as reference.

Changes: removed redundant reduction; replaced proof-construction language with direct uses of the two exact existing conclusions; added the two definition dependencies; regenerated citations.json with one literal statement excerpt per citation and corrected step numbers; corrected the failed-query verdict and added three actual independent Mathlib searches. The item's statement, the first worker's report sections, and the permitted unit realization are preserved. All reads were from the named read-only trees; no Lean, compilation, live-project writes, SGA sources or agents were used.
