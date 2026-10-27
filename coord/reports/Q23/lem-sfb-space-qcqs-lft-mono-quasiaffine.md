# Q23 stage-1 delivery: lem-sfb-space-qcqs-lft-mono-quasiaffine

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-qcqs-lft-mono-quasiaffine.json: statement unchanged; four proof steps, all citing existing nodes; split.
- citations.json: one verbatim statement quotation for each of the ten step-node citations.
- report.md: this report.

No new nodes; zero Mathlib leaves created. Existing searches retained and five searches actually run by Q23 appended from searches.jsonl. No Lean written, no compiler invoked, no repository or launcher files changed.

## Attachments

No ATTACH for the item: searches by exact blueprint tag and by algebraic-space/monomorphism/quasi-affine concepts found no project declaration covering the algebraic-space statement. The scheme result AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite at lean/WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean:106 belongs to the existing node lemma-nagata-quasi-affine-morphism-of-quasi-finite. Its closed Lean record and its proof at lines 106-111 are reused, not an attachment of the space item. Mathlib/AlgebraicGeometry/QuasiAffine.lean:29-62 concerns schemes only.

## WANTED

None. The Stacks sources used here are available locally.

## Problems found and corrected

The imported item had an empty proof. No error was found in its statement. The existing 0463 node is restricted to scheme targets; applying it directly to A -> B would be C4. The split first takes arbitrary scheme tests, then applies that node. The item defines quasi-compactness by existence of a quasi-compact atlas whereas the 073B node uses point-space quasi-compactness. Step 1 explicitly cites the continuous-surjection assertion for the forward implication and the affine-atlas existence theorem for the reverse implication on each affine test.

An early draft's scheme-theorem tag was 02L3, which tags/tags identifies as descent of open immersions. Corrected it to 02LR, more-morphisms-lemma-quasi-finite-separated-quasi-affine, before delivery. The item statement, its existing source and all imported metadata remain unchanged.

The latest blueprint proof of det-thm-sf-ctf-stability-direct-images, clause (3), supplies the compactification context. The inherited from.node is null (also returned by blueprint_refs.py ancestor), so it is retained; the precise inherited supporting place and via chain are retained. Whole-blueprint searches for quasi-affine, monomorphism and 073B found scheme statements and no equivalent algebraic-space item. same_as remains []. The unit/chapter records were read and not changed; this is not the unit's key node.

## Not duplicates

No new nodes were created. In particular, the existing scheme-target 0463 lemma, the existing 03XX representability theorem, the existing 073B permanence theorem and the closed scheme quasi-affineness theorem are cited instead of duplicated. The etale-only integral-compactification node was checked and not used for the non-etale map u.

## Review by Q23

I read spaces-morphisms.tex, lemma-quasi-compact-quasi-separated-permanence (073B), lemma-monomorphism-loc-finite-type-loc-quasi-finite (0463), proposition-locally-quasi-finite-separated-over-scheme (03XX), and lemma-quasi-finite-separated-quasi-affine (0ABS). The tags were checked against tags/tags. I also read the base-change lemma for finite type in spaces-morphisms.tex (03XH), the finite-type compatibility paragraph and base-change lemma in stacks-morphisms.tex (06FU), the two quasi-compact atlas lemmas in spaces-properties.tex (03E4 and 03H6), and the scheme theorem in more-morphisms.tex (02LR). There are no new-node sources to review.

For step 1 I opened the statements of lem-a1-space-finite-affine-subatlas, lem-sfb-space-qcqs-permanence, lem-sfb-qc-space-affine-etale-atlas and lem-sfb-stack-finite-type-calculus. The first's final sentence gives exactly quasi-compact point space from the assumed atlas; it is not used for its finite-subatlas construction. The second requires quasi-compact source and quasi-separated target, which hold for A and B. The third applies to every quasi-compact pullback point space, with no separatedness hypothesis, and supplies its affine atlas. The last explicitly gives the ordinary algebraic-space convention and its agreement with the stack convention; finite type is local finite type plus quasi-compactness on affine tests. This justifies all convention changes without assuming B affine or noetherian.

For step 2 I opened lem-trf-space-fibre-products-etale-covers and lem-sfb-stack-finite-type-calculus. The former states that the sheaf fibre product is an algebraic space. The latter states arbitrary base-change stability of finite type and agreement on algebraic spaces, so it applies to every scheme T -> B, not merely etale ones. The monomorphism argument is written out on H-sections: fixing the T-component forces equality of the A-components by u's assumed injectivity. This is elementary and needs no additional base-change-of-monomorphisms node.

For step 3 I opened lem-sfb-space-lft-monomorphism-separated-lqf and lem-a1-separated-locally-qf-space-representable. The first applies because the target is now the scheme T, not B, and it supplies both the chartwise quasi-finiteness and the closed diagonal. The second's hypotheses are exactly these assertions and it returns a representing scheme over T. Taking every T proves representability by schemes, without any unproved descent of quasi-affineness.

For step 4 I opened lemma-nagata-quasi-affine-morphism-of-quasi-finite and def-nagata-quasi-affine-morphism, and read the scheme declaration at its recorded Lean source. Its four hypotheses have been supplied: quasi-compactness by step 1, local finite type by step 2, local quasi-finiteness and separatedness by step 3. Once represented, the identity scheme chart gives the scheme properties directly. The definition applied to the affine open T itself gives a quasi-affine source, hence a quasi-compact open subscheme of an affine scheme, exactly as required by the item's definition. No representability or quasi-affineness of an algebraic space is inferred from a scheme-only statement before representation is proved.

Small cases: the empty source is allowed by every cited statement and gives the empty quasi-affine scheme on every test; the identity of any qcqs space reduces to the identity of each scheme test, including nonschematic B; a finite-type closed immersion is covered, with no finite-presentation assumption; quasi-compact open immersions are covered; a non-quasi-compact open in an affine scheme is not a counterexample because it fails the quasi-compact source hypothesis. The argument does not add noetherianity, finite presentation, or representability as hypotheses.

I checked delivery-errors B-E: there are no new statement-only nodes to malformedly populate, no restatements of the item, no uncited non-elementary input, no uses of a cited proof instead of its statement, and no hidden long step (each step is below 1000 characters). All ten citations have verbatim quotes. A read-only dependency traversal found no path from any cited node back to this item. The three off-unit tools are declared in split_report.tool_uses: point-space quasi-compactness from an atlas, sheaf fibre products, and scheme representability for separated locally quasi-finite spaces. These are generic tools and preserve the item's 073B/0463/0ABS route.

## Unfinished work

None for the stage-1 split. No sub-agent or second reader was started; this is direct delivery under the brief. The existing generic dependencies retain their own stage states.

## Validation

The server-side review_split check passed with zero new nodes; the source-tag correction and explicit fibre-product tool-use declaration were then applied. Final deliver.py --no-push and push results are recorded by the delivery tool.
