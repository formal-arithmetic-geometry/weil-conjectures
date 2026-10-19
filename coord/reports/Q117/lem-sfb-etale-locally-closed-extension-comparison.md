# Q117 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-locally-closed-extension-comparison.json`: statement, split in seven steps; no exact Mathlib match. Statement and inherited fields/searches preserved; proof, proof dependencies, search evidence and split report supplied.
- `citations.json`: 23 entries, one per step/node citation, copied verbatim from the current repository statements.
- `searches.jsonl`: actual launcher search log, retained across the interrupted turn.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. The only delivered node is the item.

## Attachments

No full-item attachment. `AlgebraicGeometry.Etale.finiteOpenComparison` (FiniteComparison.lean:169) and `AlgebraicGeometry.Etale.isIso_finiteOpenComparison` (:240) cover the finite-open clause, including its specified map, in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/Etale/LowerShriek/OpenImmersion/FiniteComparison.lean`. They belong to the already existing nodes `def-weil-pbc-finite-open-comparison` and `lemma-weil-pbc-finite-pushforward-extension-zero`; I reuse those nodes. The file contains no `sorry`. It does not state the locally closed closure comparison or compatibility with another closed immersion, so it does not attach this whole item. The item blueprint tag and locally-closed/closure terminology were searched in WeilConjectures; no full declaration was found. Master source is only reference material.

## WANTED

None. All sources used are present locally.

## Errors and scope

The item is mathematically correct and its statement is unchanged. The original proof was empty; its first clause alone was already an existing theorem. I did not create a duplicate or move any item clause into a new node.

The `sk-lem-sf-flat-model` unit JSON still names the old smooth-purity chapter and older text, whereas the item is bound to the six-functors chapter. I read both the record and the current main-20261015 unit and parent proof, and followed the latter: clause (2) of `det-sf-flat-model-generation`, identifying the first extension term and the closed-pushed induction factors. I have not changed maintainer-owned unit metadata. This is a metadata mismatch, not a mathematical reason to change the route. No forbidden literature is used in this split.

### Source error in an untouched dependency

The old `statement` of `def-nagata-scheme-theoretic-image` says “largest closed subscheme” through which the morphism factors. That is false: the image of the empty scheme in Spec(k) is empty, whereas the largest closed factor is all of Spec(k). The node's `blueprint_update.statement` already corrects this, using the largest quasi-coherent kernel ideal, hence the smallest closed subscheme. Stacks Tags 01R6/01R7 agree with this correction. I use the corrected convention and the explicit existing universal-property node, and do not edit the other worker's definition. The quasi-compactness needed for the ordinary kernel and open restriction is checked in step 3.

## Unfinished work

None in this stage-1 split. Existing cited statements remain the existing DAG's obligations; no Lean was written, compiled or built.

## Not duplicates

No new node was created. Whole-DAG/tag/keyword and blueprint searches found the finite-open theorem, its mate definition, the open-unit result, the 04CA closed-embedding theorem, the Noetherian-open tool, and the three scheme-image comparison tools. The pro-etale `lem-sfb-locally-closed-extension-coherence` does not supply an ordinary small-etale result without a separate site comparison, so it is not used. The derived compactification-independence theorem has a different coefficient/derived framework and is not used. Elementary scalar linearity, Noetherian checks, the double application of the image universal property, and direct-image associativity stay as written arguments in the item's steps.

## Review by Q117

I read `coord/brief-stage1.md`, stage 1, the three levels and tool-use rule in SETUP, GOAL, dag-sync, the chapter and unit records, and delivery-errors B–E. I compared the item with the current parent proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-sf-flat-model/det-sf-flat-model-generation.proof.md` and the current unit `_section.md`. The parent needs ordinary finite-coefficient etale sheaves, including nonreduced locally closed strata. The split keeps that category throughout; it introduces no derived or pro-etale identification.

For the item I read Stacks `etale-cohomology.tex`, Tag 0GJ1 (`lemma-compatible-shriek-push-finite`) and 0F70 (`lemma-jshriek-open`), and Tag 04CA (`proposition-closed-immersion-pushforward`). For the closure arguments I read `morphisms.tex`, Tags 01R6, 01R7 and 01R8, together with the current blueprint texts of the already existing immersion-open-in-image, closed-image and universal-property nodes. There are no new nodes whose sources need separate validation. Tags were checked in `literature/stacks-project/tags/tags`.

1. Step 1 cites closed-immersion-finite for exactly its finite conclusion, the finite-open theorem for exactly its natural isomorphism, and the finite-open definition for the actual transpose. I read all three statements. The cartesian square and both open arrows are precisely the item's hypotheses. The separately cited open-unit-isomorphism statement supplies the inverse unit, so the direction of the prescribed composite is accounted for rather than assumed.
2. Step 2 uses the direct-image section formula and extension's sheafification construction, both read in their complete definition nodes, and the module-morphism and constant-sheaf definitions. Naturality in the input sheaf gives commutation with each constant scalar; locally representing a section of the constant sheaf by constants and then gluing gives the full local-ring-section condition. An inverse of a linear bijection is linear. The inverse-image definition explicitly permits a fixed coefficient ring whose pullback is identified with itself. These are elementary consequences of the cited definitions, not a hidden coefficient-comparison theorem.
3. Step 3 cites the full Noetherian-open statement and the open/closed immersion definitions. A closed subscheme is locally affine with quotient rings, whose ascending ideal chains stabilize by pulling them back, and is a closed quasi-compact subspace. Applying the Noetherian-open statement again proves quasi-compactness of the inverse image of every affine open of X. The monomorphism and diagonal assertions follow from the written local quotient and open descriptions. Thus both quasi-compactness and quasi-separatedness are checked before the next citations, even though the current blueprint version of open restriction only requires quasi-compactness.
4. Step 4 uses exactly what its three cited statements assert: the factor into the image of a quasi-compact immersion is open; the image commutes with open restriction; the image of a closed immersion is its source over the target. I checked each statement and its relevant current blueprint text. The actual fibre product of S with W is identified by its two inverse maps, so no factorization is inferred merely from a set-theoretic inclusion. Compatibility with the maps to W follows from the cited compatible inclusions and monomorphisms.
5. Step 5 applies the already proved closed/open clause to that square and uses the open-unit isomorphism and finite-open definition to write the equation for restriction of the mate. The triangle/transpose equation makes this the identity on h_*L. The ordinary small-etale statement of `lem-kun-04ca` says that inverse image is a left inverse to closed pushforward; it supplies precisely the final identification with L. I deliberately did not cite the similarly named fully faithful O-module theorem, which is on a different site and ring. The scalar check from step 2 upgrades the abelian identification here.
6. Step 6 cites the image universal property, which expressly gives a closed comparison for every closed factorization and uniqueness, and the immersion-open result for the open factor of b. The target Y is Noetherian by the same quotient argument already written. Applying the universal property once in each ambient scheme gives the two comparison maps; their composites are identities because the closed inclusions are monomorphisms. Closure composition is therefore proved rather than cited as an unstated standard fact. Closed composition is checked on composite surjective quotient maps from the cited closed-immersion definition.
7. Step 7 reads the ordinary direct-image formula on an etale test object and writes the associativity identification of fibre products. It commutes with restrictions and module actions and has the reverse identification as inverse. This proves the functorial isomorphism directly from definitions and the closure identification in step 6; it does not require a new associativity node. The cited fibre-product definition is only used for this universal-property identification.

I checked the source-category distinctions and all of C1/C4, not just citation presence. Every theorem used is an existing cited node, and every `uses` entry has a verbatim statement excerpt in citations.json. Generic off-unit tools are declared in `split_report.tool_uses` with their exact purpose; none replaces a parent unit step. Each proof step is under 2000 characters. The zero sheaf, empty stratum/square, identity open or closed map, a closed stratum, and an open stratum specialize to the expected zero or unit/direct-image identifications. Nonreduced closed immersions are preserved: the closure square uses scheme-theoretic images and quotient maps rather than reduced supports. No extra finiteness, separatedness of X, invertibility of |A|, or constructibility hypothesis was used.

The preserved Q45 searches are inherited evidence. The five Q117 searches are the exact commands/results in searches.jsonl: two semantic phrasings, Loogle, LeanSearch and grep. I read the reported types: scheme lift/immersion results and Zariski module restriction do not prove the item; the generic sheaf-module pushforwardComp result gives only the elementary sectionwise associativity in step 7. I read the candidate Mathlib source at `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:139` and `AlgebraicGeometry/Modules/Sheaf.lean:348`; neither supplies closed/open etale extension comparison or closure independence. Thus the item remains a split statement, with no invented Mathlib leaf or logged search.

### Resumed dry-run repair

The resumed dry run rejected the two direct-image quotes (steps 2 and 7) because each contained only the displayed formula, fewer than 40 characters. I replaced both with the complete ordinary direct-image paragraph, including the section formula, restrictions, action on morphisms and functor. These are verbatim excerpts of the current dependency statement. The seven-step proof and all inherited searches are unchanged. On resumption I compared the sandbox against the current repository: only split-owned fields differ, all 23 citation excerpts are verbatim, the proof dependencies equal the union of step citations, and the longest step is 1118 characters. I reread the current parent proof clause (2), the three scheme-image tool statements, Stacks 0GJ1/0F70/04CA and 01R6–01R8, and the existing finite-open Lean declarations. They confirm the source and category checks described above.

The next server preflight rejected the phrase “the item’s specified transpose” in step 1 as a non-self-contained reference (B2). I replaced it with the full composite $u^*g_*v_!L \to h_*v^*v_!L \to h_*L$ and the adjunction specifying its transpose. This changes only the explicitness of the proof text, with the same citations and unchanged statement.
