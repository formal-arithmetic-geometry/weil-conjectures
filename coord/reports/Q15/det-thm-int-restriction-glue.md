# Worker report: det-thm-int-restriction-glue

## Files written

- `dag/nodes/sec-six-functors-basics/det-thm-int-restriction-glue.json`: rebased split of the current imported two-clause statement, with eight proof steps and no new nodes.
- `citations.json`: verbatim statement evidence for every cited node in every step.
- No Mathlib leaves or auxiliary nodes.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` tree for the item id, the statement's exceptional-adjoint terminology, and the nearby integral restriction declarations. No sorry-free declaration states both clauses of this item. The nearby integral exceptional-adjoint declaration contains `sorry` and is not an attachment.

## WANTED

None.

## Findings and corrections

The returned delivery was reviewed successfully but could not land because `det-prop-int-brown-adjoint` had changed. I compared the retained split with the current DAG, read the current statement of that node, and rebased the item onto the current imported statement. The authoritative item statement is retained mathematically: finite-open locality for module-object `Dbc`, preservation of `Dbc` by `f^!`, and restriction of the Brown adjunction. The retained proof route remains the integral module-object route and does not introduce a derived-complete coefficient category.

I also reread the current `det-thm-restriction-local` statement. Step 5 now explicitly instantiates it at its allowed coefficient `\Lambda=E` to obtain the finite affine chart data; it does not claim that the theorem's conclusion is coefficient-independent. The two stale quotes of `det-prop-int-brown-adjoint` in steps 6 and 8 were replaced by verbatim text from its current statement, including its ambient localizing categories, Hom adjunction, uniqueness, and `\Dctf=\Dbc` identification. The latest full dry run detected two further stale quotes, for `det-def-localizing-closure-ctf-equals-bc` in Step 6 and `det-thm-int-restriction-line` in Step 7; I replaced them from the current statements and checked all 21 quotes against the local DAG again.

The proof is one level: Steps 1–4 prove finite-open locality by exact restriction, global bounds, finite stratification refinement, and the defining bounded-constructible conditions. Step 5 obtains affine presentations. Step 6 derives the local formula for `u^*f^!` from integral open adjunctions, compact-support composition, and uniqueness of right adjoints. Step 7 applies the integral affine-space and closed-immersion results, then Steps 1–4 to glue. Step 8 restricts the Brown adjunction using preservation by `Rf_!`, preservation of `f^!`, and fullness.

## Unfinished work

No proof step or citation remains unfinished. No Lean source, compiler, Lake, or shared repository was modified.

## Not duplicates

No new nodes were created.

## Review by Q15

I read the current item node, its blueprint statement and proof, the enclosing `sk-thm-int-restriction` unit, and every node cited by the eight retained steps. For Steps 1–4, `lem-weil-proetale-weakly-etale-localization`, the completed coefficient limit, and exact module restriction justify restriction of cohomology; `sk-def-sfb-bounded-constructible`, `sk-def-sfb-constructible`, `sk-def-sfb-dc-setting`, and the pro-etale site definition supply the bounds, finite local models, and covering argument. I checked the empty-cover case and the finite intersection refinement, including that each final stratum lies in a cover member carrying its stated local model.

For Step 5 I read the full current `det-thm-restriction-local` statement and verified that setting `\Lambda=E` gives exactly the finite affine opens, closed immersion, projection, and factorization used. For Step 6 I reread `det-def-localizing-closure-ctf-equals-bc`, `det-sf-mate-open-restriction`, the current integral Brown construction, and the changed Brown adjoint. Their statements provide the localizing categories, open `w^!\simeq w^*`, compact-support composition, the right adjoints, and uniqueness; the displayed Hom chain therefore has the correct order and variance. For Step 7 I checked that `sk-lem-int-tensor` puts `v^*K` in integral `Dbc`, while the affine-space and closed-immersion nodes put the next objects in `Dbc` before they are used. For Step 8 I verified from the current Brown construction and adjoint that both functors preserve the required subcategories and that the ambient Hom bijection restricts along the full inclusions stated by the bounded and localizing definitions.

Every `uses` entry has a verbatim quote in `citations.json`, and `proof_deps` is exactly their union. The dependency graph has no path back to this item. The repair rebases to the current imported statement, refreshes the current-node citations, corrects the chart wording, and spells out the general-to-integral adjoint identification and counit-compatible uniqueness in Step 6. The changed equality theorem still applies to the qcqs standing schemes with the same pulled-back condensed coefficient; the changed affine-space theorem still states both the functor isomorphism and Dbc preservation for every natural dimension, including zero. Its expanded standing hypotheses are exactly those checked in Step 5. No new fact is taken from either node’s proof.

The returned citation check also required the two construction citations to quote only the precise composition and Dbc-preservation sentences used by Steps 6 and 8; I narrowed those quotes to those verbatim sentences and rechecked them against the current node.

The latest full preflight identified an imported dangling statement reference: `[sk-prop-int-brown]` is a unit id with no node. I corrected that reference to `[det-prop-int-brown-adjoint]`, already a statement dependency. I reread its natural Hom bijection on the integral module-object localizing categories and verified it is precisely the adjunction named in clause (2); the statement’s hypotheses and conclusions are unchanged.


## Current DAG revalidation

After the landing refusal, I compared every citation against the current shared DAG. The current `det-thm-int-restriction-closed` statement has a full standing-setting preamble and names the integral Brown adjoint; Step 7 now quotes that exact current statement. The current `sk-def-sfb-bounded-constructible` statement was also expanded, so its quotes in Steps 2, 4, and 8 were refreshed verbatim. All 24 citation entries now contain exact substrings of their current cited statements; no proof dependency or step text changed. `srvcheck.py` returned `check_dag OK` and `review_split ... PASS`.

## Earlier second reading (a previous round; superseded)

- Item statement: checked both clauses against `main-20261015/.../sk-thm-int-restriction-glue.md` and the standing scheme/coefficient definitions; pass. Replacing the unit pointer by `det-prop-int-brown-adjoint` changes no hypothesis or conclusion. The source proof's derived-completeness paragraph is unnecessary for the actual module-object definition, which explicitly imposes no completeness condition; the retained bounded-cohomology proof proves the stated category instead.
- Step 1: checked the site equivalence and constant-ring restriction clauses of `lem-weil-proetale-weakly-etale-localization`, all three integral-limit clauses, and exact restriction in `lem-pur-site-restriction-module-adjunction-exact` against Stacks `more-morphisms.tex`, labels `lemma-composition-weakly-etale` (094T) and `lemma-weakly-etale-permanence` (0951), and `sites-modules.tex`, label `lemma-extension-by-zero` (03DJ); pass. Sectionwise restriction preserves limits, and exact restriction commutes with kernels and cokernels, hence cohomology.
- Step 2: checked boundedness against `sk-def-sfb-bounded-constructible` and the covering condition against `def-weil-pbc-proetale-site`; pass. The minimum/maximum argument and sheaf uniqueness are elementary, including the zero complex and the empty-cover/empty-scheme case.
- Step 3: checked finite local scalar models against `sk-def-sfb-constructible`, finite-type Noetherianity against the existing leaf `lem-weil-pbc-finite-type-over-noetherian` and Stacks `morphisms.tex`, label `lemma-finite-type-noetherian` (01T6), and constructible locally closed subsets against `def-weil-constructible-subset` and `topology.tex` (005G, 005H, 005L); pass after explicitly citing the latter two nodes. Intersections of finitely many open-intersect-closed subsets remain locally closed and refine the finite partitions. For each resulting stratum choose a cover member containing it, pull back its trivializing covering, and use its same finite scalar matrix; this also checks a one-point scheme and the empty strata.
- Step 4: checked the exact boundedness-plus-constructible-cohomology definition and fullness in `sk-def-sfb-bounded-constructible`; pass, with no derived-completion assumption added.
- Step 5: checked the final existence sentence of the current `det-thm-restriction-local`, at its allowed coefficient E, against the actual finite affine data used, and the standing k-scheme hypotheses; pass after citing the same Noetherian leaf for quasi-compact opens. Only the geometric existence clause is used, not its rational exceptional-pullback assertion.
- Step 6: read the current full statements of `det-def-localizing-closure-ctf-equals-bc`, `det-sf-mate-open-restriction`, `det-prop-int-brown-construction`, and `det-prop-int-brown-adjoint`; pass after replacing the stale open-restriction quote. The current open theorem expressly allows O_E and identifies j^! with j^* on Loc(Dctf); the category equality and the Brown-adjoint identification put it on exactly the integral categories here. The displayed Hom chain composes the adjunctions with the stated compact-support composition, so uniqueness gives the written inverse-order composition of right adjoints. Its application has qcqs targets and quasi-compact open immersions by Step 5.
- Step 7: checked inverse-image preservation in `sk-lem-int-tensor`, clauses 2 and 3 of the current `det-thm-int-restriction-line`, and the full statement of `det-thm-int-restriction-closed`; pass. Each successive input is bounded constructible before applying the next result. For d=0 the twist and shift are zero and the affine-space formula is the identity; for d=1 it is exactly the affine-line case. Step 1–4 apply to the ambient object underlying the Brown output.
- Step 8: checked the precise Dbc-preservation sentence of `det-prop-int-brown-construction`, natural Hom bijection of `det-prop-int-brown-adjoint`, and fullness in both category definitions; pass. The same Hom bijections, unit and counit restrict, an elementary consequence of fullness and the two preservation statements.
- New nodes: none; B1–B7, duplicate elimination, and new-node edge cases are vacuous. The two newly explicit dependencies already exist as Mathlib leaves, so this delivery creates no nodes and no leaves. Independent LeanFinder and grep searches, recorded as returned in `searches.jsonl`, found sheaf-adjunction and constructible-subset declarations only. I read `Mathlib/Topology/Constructible.lean:504–539`: those hits concern subsets, not constructible sheaves or either clause of this item. The nearby slopmaster2 integral exceptional-adjoint declaration still contains sorry and is not an attachment.

Changes: refreshed the Step 6 open-restriction quote to its current statement; added the existing Noetherian leaf in Steps 3 and 5 and the existing constructible-subset leaf in Step 3; updated the citation evidence and dependency union; recorded independent searches. The original review and correct proof steps remain in place. No statement dispute or new source error was found.

## Second reading by Q15

- Item statement: compared both clauses with the main-20261015 statement, its proof, unit proof, and standing setting; pass, with only the previously documented unit-to-node Brown reference repair. The actual coefficient category is the module-object Dbc defined by sk-def-sfb-constructible, not a category defined by derived completeness.
- Step 1: checked all three cited statements, Stacks more-morphisms.tex labels lemma-composition-weakly-etale (094T) and lemma-weakly-etale-permanence (0951), and sites-modules.tex labels lemma-extension-by-zero (03DJ) and lemma-extension-by-zero-exact; pass. Exact restriction computes cohomology and sectionwise restriction preserves the coefficient inverse limit.
- Step 2: checked boundedness in both constructibility definitions and coverings in def-weil-pbc-proetale-site; pass, including zero objects and the empty scheme with the empty cover. The finite minimum and maximum supply uniform bounds.
- Step 3: checked scalar presentations in sk-def-sfb-constructible, the standing hypotheses, Stacks morphisms.tex lemma-finite-type-noetherian (01T6), and topology.tex definition-constructible, lemma-constructible, lemma-constructible-Noetherian-space (005G, 005H, 005L); pass after spelling out the scheme structures and pullback calculation. Finite fibre products realize the intersections and provide maps to the original strata. Pullback of a finite scalar matrix gives the same finite scalar presentation. Empty strata are discarded; the one-point and zero-module cases satisfy the argument.
- Step 4: checked the boundedness and constructible-cohomology conditions against the cited full-subcategory definition and the specific Dbc definition in the statement; pass.
- Step 5: checked the complete current det-thm-restriction-local statement at its permitted coefficient E and Stacks 01T6; pass. Only the finite affine-presentation existence clause is used. All chart schemes and arrows stay in the standing setting, and chart opens are quasi-compact.
- Step 6: checked every displayed Hom set against the current category-equality, open-restriction, Brown-construction, and Brown-adjoint statements; pass. The open theorem permits integral coefficients, the equality node identifies both localizing categories, and counit-compatible uniqueness gives the stated inverse order of right adjoints.
- Step 7: checked the full statements of sk-lem-int-tensor, det-thm-int-restriction-line (clauses 2 and 3), and det-thm-int-restriction-closed; pass. Every input lies in Dbc before the next theorem is applied. Dimensions zero and one give the identity and affine-line cases.
- Step 8: checked Dbc preservation in the Brown construction, the natural Hom bijection in the Brown adjoint, and fullness in both definitions; pass. Independently found and read Mathlib/CategoryTheory/Adjunction/Restrict.lean:29–70, including Adjunction.restrictFullyFaithful:42; its generic statement confirms this elementary argument and supplies no theorem proving the complete item.
- New nodes: none; new-node source, duplication, form, and Mathlib-leaf checks are vacuous. Independent LeanFinder and grep queries are recorded as returned in searches.jsonl; the nearby integral exceptional-adjoint source theorem is still sorry-based and concerns a different coefficient category, so is not an attachment.

Changes in this reading: made Step 3 use fibre products to realize the refined strata and wrote the finite-matrix pullback calculation instead of leaving the preservation assertion implicit; recorded independent searches and this review. All 24 citation quotes were checked verbatim against the current shared DAG, and every step citation is covered. No node, Mathlib leaf, hypothesis, or conclusion was added. The original Review by Q15 remains intact.
