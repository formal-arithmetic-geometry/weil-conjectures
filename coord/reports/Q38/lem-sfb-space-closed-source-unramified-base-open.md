## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-source-unramified-base-open.json` (statement, split, not a Mathlib leaf), `citations.json`, and this report. No new nodes, no Mathlib leaves, no Lean files.

Attachments: none. The item-id search in `lean/WeilConjectures/` is empty. Concept searches found scheme unramified-open restriction results, including `AlgebraicGeometry.unramified_baseChange_restrict_open` in `AlgebraicGeometry/Morphisms/UnramifiedBaseChangeOpen.lean`; reading that file shows a scheme restriction/base-change theorem, not this algebraic-space parameter-open assertion. There is no attachment of the whole item.

WANTED: none. All sources used are present locally.

The imported item had no proof. Its statement agrees with Stacks 05X8 (spaces-more-morphisms.tex, lemma-where-unramified), including merely closed, not universally closed, source map and arbitrary algebraic-space parameter changes. The statement and its dependencies are unchanged. No statement dispute or unit-route error was found. The split fills in the source's final immediate inference: point lifting proves equality of the images of the bad loci after arbitrary base change; closedness is used only before changing the base.

Nothing remains unfinished for this stage-1 item. Every proof input already exists; those nodes retain their own independent stage status.

## Searches and blueprint

I read and retained the item's five recorded Mathlib searches from 2026-10-23, including their returned results: two LeanFinder phrasings, LeanSearch, Loogle `"unramifiedLocus"`, and grep `where.*unramified|unramifiedLocus|Unramified.*[Ll]ocus`. Their ring-theoretic and scheme hits do not give the algebraic-space universal parameter open. The search question and statement have not changed, so these searches were not repeated or relabelled as new searches.

Whole-DAG source-tag searches for 05W2, 03BZ, 03IE and 05X8, and searches for finite-type cancellation and fibre-product point lifting, found all inputs already present. In particular `lem-sfb-space-unramified-locus-base-change` supplies the locus and its target-base-change formula, and `lem-sfb-space-lft-cancellation` supplies the missing local-finite-type hypothesis. The similarly named `lem-sfb-closed-source-unramified-parameter-open` states only the scheme case, so does not subsume the item. I opened it and reused no assertion beyond its statement.

`blueprint_refs.py search` was run for 05W2, 03BZ, 05X8, unramified, open subspace, fibre product points, finite type and finite type cancellation. There is no imported blueprint node with this full space-family statement. `ancestor` returns None; the existing null ancestor, precise inherited place and via chain are preserved. I read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`: paragraph (3) is the ambient direct-image/compactification route. This item is its inherited lower-level Hilbert-lci/moduli prerequisite, not a replacement of the fixed unit route.

## Not duplicates

No new nodes. In particular no second copy of the source-locus theorem, the point-lifting theorem or the open-subspace correspondence was made. The existing scheme parameter-open statement requires schemes, whereas the item allows all three spaces and arbitrary space parameter changes.

## Review by Q38

I read Stacks 05X8, spaces-more-morphisms.tex lemma-where-unramified, statement and proof, against the item. It assumes exactly that p is locally of finite type and closed. It does not assume flatness, separatedness, properness or representability by schemes of p or q. I also read spaces-morphisms.tex lemma-where-unramified (05W2), including its distinction between the parameter base Z and the target Y, and lemma-permanence-finite-type (0462). For open spaces I read spaces-properties.tex lemma-open-subspaces (03BZ) and lemma-factor-through-open-subspace (03IE). The source's final inference is made explicit with the existing 03H4 Cartesian-points statement, not with any assertion that the point functor preserves fibre products bijectively.

Step 1 uses the exact cancellation conclusion of `lem-sfb-space-lft-cancellation` for u followed by q. Its statement imposes no condition on q. This establishes the locally finite type hypothesis of `lem-sfb-space-unramified-locus-base-change`, whose statement explicitly supplies a largest open with unramified restriction and identifies its point set. I opened both node files. It would be incorrect to apply a locally finite type locus theorem directly without this cancellation.

Step 2 uses the open-embedding clause of `lem-a1-space-point-open-calculus` to know that |U| is open. Closedness of E is precisely the hypothesis on |p|. I opened `lem-a1-space-etale-open-image`: its statement explicitly gives the inclusion-preserving bijection for all open subspaces and all open subsets, independently of its subsequent etale-map clause. Only that initial clause is used to construct W. No closed subspace structure on the bad subset D is required.

Step 3 uses `lem-trf-space-fibre-products-etale-covers` only for actual fibre products of algebraic spaces. I checked its statement gives existence and the categorical universal property. The identification A times_B B' = A times_C (C times_B B') is spelled out on scheme tests using q u = p. This is the base change of u along C' to C, precisely the target-base-change formula in the statement of `lem-sfb-space-unramified-locus-base-change`. I did not ask that node for a parameter-base formula it does not state. `lem-a1-space-open-factor-scheme-tests` then states the inverse-image formula for the underlying open set, so complementing gives D'.

Step 4 uses the arbitrary-morphism, arbitrary-space Cartesian-points surjection in the statement of `lem-a1-space-point-open-calculus`. Both directions of the image equality are written. The lifted point remains bad because its projection is the chosen a in D. In particular neither representability nor closedness of the changed map p' is used. The equality is a short application of the cited theorem and set membership, with no hidden lemma.

Step 5 uses exactly the largest-open-with-unramified-restriction clause of the locus statement, and the full-point-image-implies-equality clause of the point/open calculus. `lem-a1-space-open-factor-scheme-tests` states unique factorization from the point-image containment; the reverse follows by composition of point maps. The last scheme clause uses the identity scheme test in `def-a1-space-open-subspace`, which I opened: it says every scheme pullback is represented by an open subscheme. This gives an open subscheme when B itself is a scheme. No definition node is being used as an unproved geometric theorem.

All non-elementary inputs appear in the steps' uses, and proof_deps is their union. `citations.json` contains a verbatim statement excerpt for every citation, using the whole statement when several clauses are needed. No step exceeds 2000 characters. No new statement has to be checked; for the existing item I checked empty A (W=B), empty B' (vacuous factorization and unramifiedness), u an isomorphism (W=B), and a non-unramified map over a field, such as the dual-number line over that field (W empty, and nonempty field extensions remain bad). Fibres absent from A are allowed and belong to W. These cases also test the direction of the complement formula.

The cross-unit a1 statements and the trf fibre-product result are declared in split_report.tool_uses with the exact generic clauses used. They are geometric tools for the Stacks proof, not a change to the alteration/direct-image route. No maintainer-owned tool_uses or reviewed field was written. No SGA source is used. I corrected the potential misuse of the source-locus theorem by explicitly proving local finite type first and identifying the target base change before applying its formula. There are no new nodes concealing the item's clauses, no hollow definitions and no dropped hypotheses.
