# Q110 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-invertible-section-fibre-correction.json`: statement, split in four steps using existing nodes; fresh Mathlib searches found no exact match. Statement, statement dependencies and original metadata retained.
- `citations.json`: five step/node entries containing verbatim text from the cited statements.
- `report.md`: this report. `searches.jsonl` is the search command's original log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project under `lean/WeilConjectures/` by the exact blueprint tag, invertible/global-generation/section terminology, and nonvanishing constructions. The existing affine finite-generation and invertible fibre-criterion declarations prove inputs, not the correction assertion. In particular `AlgebraicGeometry.Scheme.Modules.affine_finiteType_generatingSections` belongs to the existing `lem-weil-pbc-affine-finite-type-generating-sections`; it is reused without changing that node.

## Literature wanted

None.

## Findings and changes

The item is true as stated. Its imported proof was empty. Stacks 0F20 (`properties-lemma-quasi-affine-invertible-nonvanishing-section`) supplies the intended argument: global generation gives a section nonzero at a chosen point, and addition of a section vanishing at the old points preserves previous values. Here the supplied function f makes that second section explicitly f times t. I kept the affine specialization and did not use the stronger quasi-affine nonvanishing assertion or the parent finite-set result, either of which could create a cycle.

Searched the entire DAG's statements for affine global generation and generating stalk/fibre criteria, as well as the source Lean library. Blueprint searches `globally generated`, `affine.*generat|generat.*affine`, `nonvanishing` and `finite generating` did not reveal a blueprint node stating this correction assertion. The whole-DAG search found the two precise existing helper nodes used in the proof. No new node is needed; quotient nonzeroness and the field calculation are elementary steps, not new lemmas.

`tools/blueprint_refs.py ancestor` prints None for this pre-existing non-blueprint chain. Its inherited `blueprint.from.node: null` is retained, with the already precise `from.place` and `via`; `same_as` is [] and the split report records how the proof realizes the source passage. The chapter and unit records were read and are not changed. The fibre criterion is declared in `split_report.tool_uses` as a generic tool from another unit; the affine generation node is already Lean-closed.

Fresh msearch queries were run with leanfinder, loogle, grep and leansearch and are recorded exactly in the command log and appended to the item's original search records. The second leanfinder phrasing searched affine residue-fibre generation rather than correction. I read all returned hits. PicardGroup.lean:380 and :901 concern abstract invertible modules and localizations or ideal representations; residue-field evaluation hits concern scalar structure-sheaf sections; smooth manifold section hits concern another category. None states the requested global correction. The semantic result `ModuleCat.Tilde.smul_section_apply` was not found by the pinned source grep and was not used as a match. There was no unavailable fresh service. Earlier recorded searches remain unmodified.

## Unfinished work

None at stage 1. No Lean files were written and no compiler, Lake, or build was run.

## Not duplicates

No new nodes, so there are no new/existing pairs to justify. Existing statements are reused rather than restated in helper nodes.

## Review by Q110

I read Stacks properties.tex, the entire proof of Tag 0F20, especially its n=1 global-generation argument and the final induction paragraph adding s+s'. I also read properties.tex Tag 01PB (`properties-lemma-finite-type-module`), schemes.tex Tag 01IA (`schemes-lemma-quasi-coherent-affine`), and modules.tex Tags 01AM (`modules-definition-globally-generated`) and 01CY (`modules-lemma-s-open`). These support exactly affine generation and the nonzero residue interpretation used here. There are no new-node sources to review.

Step 1 uses the actual statements of `def-sc-invertible-module`, `pqf-def-coherent`, and `lem-weil-pbc-affine-finite-type-generating-sections`. The first explicitly includes quasi-coherence and local rank one; a local trivialization is a rank-one free surjection, so it satisfies the second's finite-type definition. The third assumes only affine plus finite-type quasi-coherence and explicitly gives finite global generators. Thus all of its hypotheses hold, with no Noetherian, closed-point, separatedness beyond affineness, or finite-type-over-a-field hypothesis. This step is non-elementary because it applies affine global generation, not merely its definition.

Step 2 reads and uses the statement, not the proof, of `lem-weil-pbc-invertible-generating-sections-fibre`: a finite family generates iff some member has nonzero residue at each point. Its n+1 indexing is handled by adjoining zero to the finite family, and surjectivity remains because projection onto the old summands is surjective. The item has a chosen point z. On this repair I use the current statement's explicit germ formulation $s_y\notin\mathfrak m_y\mathcal L_y$ directly: by the definition of the quotient it is precisely nonzero residue. The former tensor/quotient comparison is no longer needed. It produces a section nonzero at z; it does NOT assert that the map from global sections onto the whole residue fibre is surjective. That stronger assertion would be false at the generic point of Spec Z for the trivial line bundle.

Step 3 uses `def-weil-residue-field`, whose statement explicitly calls kappa(z) a field and identifies it with the local-ring quotient. Germs and quotient maps preserve the addition and scalar action by their definitions, giving the displayed evaluation identity. Nonvanishing follows by multiplying a hypothetical equality f(z)t(z)=0 by the inverse of the nonzero scalar f(z). I checked that cancellation occurs in the residue-field vector space, not in Gamma(X,O_X), which may have zero divisors. Step 4 uses only that same evaluation identity and f(x)=0, and proves equality at every x in F. Both steps are elementary, with their calculations written out, and do not hide a geometry input.

I checked delivery-errors B through E against the node and the open source passages. There are no unsplit helper statements carrying hidden proofs, no renamed clauses, and no new definitions. Each cited statement was opened; each citation is represented by an exact copied substring (the complete statement) in citations.json. The non-elementary proof steps are under 2000 characters and contain no separate omitted standard argument. The proof dependencies are exactly the union of step uses. No parent depending on this item is cited, and no SGA source is used.

Small cases: if X is empty the hypothesis z in X is impossible. If F is empty, the equality clause is vacuous. F cannot contain z because f(z) is nonzero while f vanishes on F. A zero-length generating family is accommodated by adding zero; the fibre criterion at z then rules that case out. Generic points and nonclosed points are allowed; the proof needs nonzero generation, not surjectivity of global evaluation. Nonreduced schemes and functions that are zero divisors are allowed because only the nonzero residue f(z) is inverted. The trivial bundle on Spec of a field gives t=1 as a direct model. I found no statement dispute and made no statement correction.

The first dry run rejected the phrase “as in the item” in step 2 under the self-containedness rule B2. I replaced it by the explicit quotient notation $L(z)=L_z/\mathfrak m_zL_z$; the identification formulas and mathematical argument are unchanged.

## Repair of the returned delivery (2026-10-23)

The return names reviewed branch head `8377d6e5a2f` and reports a side completion not promoted to the live queue. The retained sandbox carries the four-step proof and the earlier dry-run receipt `78ecfc9f725`. I preserved its argument, citations, searches and prior review. The required initial dry run completed successfully at `386ebb37fb3`; deliver.py builds against the current origin/sheaf-dag, rather than re-pushing the returned branch. The current shared item is still `unsplit` with an empty proof; there is no released repair-note record or live completed declaration superseding this assignment. Its statement, statement dependencies, source, creation and blueprint route agree with the retained version. Those fields are retained.

I re-read every dependency, including the definitions `def-pc-scheme`, `def-sc-invertible-module`, `def-weil-residue-field`, and `pqf-def-coherent`, and the two generation lemmas. All five existing citations remain verbatim substrings of the current statements. In particular the current affine-generation lemma still assumes only affine, quasi-coherent and finite type and gives a finite generating family. The current fibre criterion gives both the residue formulation and the equivalent explicit germ condition. The coherent-definition blueprint update retains precisely the local finite-free-surjection finite-type clause used in step 1; no coherent or finite-presentation hypothesis is invoked. The two generation nodes' current Lean records point at their upstream WeilConjectures modules, whose theorem statements I also read; these remain inputs, not an attachment for this correction assertion.

The proof is adjusted substantively in step 2: instead of introducing the tensor/quotient identification, it now takes the explicit germ condition from the current cited statement and applies the definition of zero in the quotient. This is the same route and conclusion with a smaller interface requirement. Steps 1, 3 and 4 continue to apply with exactly the original hypotheses. No dependency proof is used as an unstated theorem. No new node, search question, or statement changed, so the original logged search results are reused. All non-elementary steps are below 2000 characters; the empty-scheme, empty-subset, zero-generator-family, nonclosed-point and zero-divisor checks above still apply. The mathematical adjustment and this repair account distinguish this delivery from an unchanged re-push. Promotion of side completion remains the maintainer's operation.
