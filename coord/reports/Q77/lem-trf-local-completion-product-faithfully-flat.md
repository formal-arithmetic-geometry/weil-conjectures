## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-completion-product-faithfully-flat.json`: statement, split into five steps; no exact Mathlib match for the combined cover theorem. Every cited input is an existing Mathlib leaf.
- `citations.json`: six entries, one per step/cited-node pair, quoting the actual dependency statements verbatim.
- `searches.jsonl`: the search command's four actual outputs; existing item search records were retained.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, for faithful-flatness terminology, and for completion/product combinations. No project declaration states this cover theorem. I also checked the read-only master source by id. Its reference declarations are not treated as completed proofs.

## WANTED

None. All sources used are in `literature/stacks-project/`.

## What changed and what was wrong

The inherited node was statement-only, with no proof. Its mathematical statement is correct and is exactly the cover assertion in `flat.tex`, Tag 05FS, `lemma-fibres-irreducible-flat-projective`, proof, lines 2216–2222. The source points to 00MB, which supplies flatness of completion but does not by itself state the faithful flatness of the product. The split supplies the missing maximal-ideal argument explicitly. I kept reducedness and the condition f nonzero although the argument works without them. I added only the citation defining A_f and its `stmt_deps` entry; no mathematical hypothesis or conclusion changed.

The item already has a specific `blueprint.from.place` and a long inherited ancestry chain; these were retained. Its ancestor is `lem-trf-local-term-locality`, as confirmed by `tools/blueprint_refs.py ancestor`. The current parent `lem-trf-local-noetherian-fibres-projective` uses this cover at Step 5. This remains a generic algebra input of the inherited semistable-alteration branch of `sk-i-curve-zero`; it replaces no step at the unit or chapter level. The unit's `realized` fields do not belong to this item and were not changed.

## Mathlib and duplicate searches

I read the source hits for `AdicCompletion.flat_of_isNoetherian` (`AdicCompletion/AsTensorProduct.lean:379`) and `IsLocalization.flat` (`Flat/Localization.lean:37`): they prove component flatness only. Loogle returned no combined theorem. LeanFinder and the differently phrased LeanSearch query returned component flatness and generic faithful-flatness criteria. The grep hit in `Regular/RegularSequence.lean:548` is an unrelated TODO about regular sequences under localization/completion. None is the product-cover assertion or a one-line specialization of it: the two residue-field maps and the maximal-ideal case split are still necessary. Queries and actual summaries are appended to the item, with the exact query strings kept in the command's log.

Before deciding on dependencies, I searched all DAG nodes for 05FS, 00MB, completion, localization-flatness, product-flatness and faithful-flatness criteria. This found the six existing inputs used below, so no auxiliary node was created. Whole-blueprint searches for `05FS`, `completion product faithfully flat`, `faithfully flat` and `completion` found no blueprint node stating the cover. In particular, local-completion-faithfully-flat assumes a local base ring, whereas this item has arbitrary Noetherian A and needs the localization factor. The Noetherian-completion-flat node gives only flatness and is reused, not duplicated.

## Not duplicates

No new nodes were created, so there are no new-node/existing-node pairs to justify.

## Review by Q77

I read the item's source paragraph in full, including the reduction to reduced R, choice of nonzero f by generic freeness, the displayed cover, and the subsequent projective-descent application. I also read the chapter and the full `sk-i-curve-zero` unit, the parent node and its completion-cover step. The cover is an algebraic tool on that branch and does not alter the geometric unit route. No SGA source is used.

For Step 1 I opened both cited node statements. `lem-weil-pbc-localization-flat` asserts flatness for every multiplicative-subset localization, so it applies to the powers of f even when f is a zero divisor. `lem-weil-pbc-noetherian-completion-flat` asserts flatness of completion at any ideal in a Noetherian ring, so it applies to I=(f). I checked its source, Algebra 00MB, part (1), and localization source 00HT, part (1). Neither input requires A local or f regular.

For Step 2 I opened `lem-weil-pbc-finite-product-flat-modules`: its statement is precisely the needed assertion for n=2 with componentwise A action. The ring map gives this same action on B. This is cited as a theorem, not hidden as an elementary flatness claim.

For Step 3 I read `def-weil-ring-localization-away`, including its equality criterion and fraction operations (00CO). The map to A/m is written explicitly. Maximality makes A/m a nonzero field; f outside m makes its residue invertible. The fraction equality implies equality of values by cancellation in that field, and the fraction operations prove the map preserves addition and multiplication. Thus the composite B→A_f→A/m is unital and kills the generators of mB; mB cannot contain 1. This is an elementary fraction calculation, not an invocation of prime-lifting or a universal-property theorem absent from the cited statement.

For Step 4 I read `lem-weil-pbc-adic-completion-mod-ideal`: its clause (2) supplies exactly the projection to A/(f) and its compatibility with A→C. Its hypothesis is finite generation of I; the single generator f verifies it. I checked Algebra 05GG (`lemma-hathat-finitely-generated`), n=1, and the related projection argument in 00MC. As f belongs to m, reduction A/(f)→A/m is well-defined. The composite through the second projection of B kills mB and sends 1 to 1 in the nonzero field A/m. No assumption that (f) is in the Jacobson radical of all A is made; in particular I do not apply the local-completion-faithful-flatness lemma to a nonlocal ring.

For Step 5 I opened `lem-weil-pbc-flat-faithfully-flat-maximal-ideals` and read Algebra 00HP (`lemma-ff`), implication (4)⇒(1). Its hypotheses are precisely flatness from Step 2 and propriety of the extended ideal for every maximal ideal, established by the exhaustive cases in Steps 3–4. No additional surjectivity-of-spectra theorem is used. Every cited statement is quoted in citations.json; all six dependencies are existing unmerged Mathlib leaves, so no off-unit non-leaf tool declaration is needed.

I checked B–E of delivery-errors against these files. There are no statement-only auxiliary nodes, no restatement nodes, no hidden comparison maps, no new unattested searches, and no proof step exceeds 2000 characters. The two elementary fraction/ideal arguments are written out where used, rather than promoted to nodes. I checked the edge cases: if f is a unit, C=0 and A_f=A, so the cover is the isomorphism A→A×0; for A=k×k and f=(1,0), f is nonzero but a zero divisor and the two factors recover the two field components; for A=Z and f=2, the two maximal-ideal cases distinguish (2) from every other maximal ideal. The zero ring has no nonzero f and is excluded by the original hypotheses. These checks confirm that neither injectivity of A→C nor regularity of f was silently assumed. I made no statement correction beyond adding the missing localization citation.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake or build tool was run. Delivery dry run and push follow this review.
