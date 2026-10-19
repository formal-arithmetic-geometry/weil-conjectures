## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-flat-valuation-lifting.json`: statement, split into six steps; Mathlib search found component lemmas but no exact or one-line match for the whole assertion.
- `citations.json`: verbatim statement excerpts for every step citation (whole statements retained to include all hypotheses).
- No new DAG nodes; no new Mathlib leaves. All supporting facts already have nodes.

## Attachments

None. Searching the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id and by flat/valuation/lifting found no declaration stating the item. The upstream declaration-name table likewise has no entry for this item. Mathlib valuative criteria concern a specified generic arrow and specializing maps, not this lifting through an arbitrary flat morphism after extension of valuation rings.

## WANTED

None.

## Corrections and scope

The item was a statement-only node, with no proof. Its statement is correct and unchanged. The proof is now the scheme specialization of Stacks 089F (`spaces-morphisms.tex`, `lemma-lift-valuation-ring-through-flat-morphism`, lines 8740–8775). The atlas in that algebraic-space proof is unnecessary for a scheme. We retain its actual route: base change, flat local stalk map, prime over zero, dominating valuation ring. The meaning of extension is checked against `more-algebra.tex`, `definition-extension-valuation-rings`: injective and local, not a finite or discrete extension.

The item's inherited chapter/unit binding and blueprint ancestry are retained. This is a generic algebraic-geometric input below the representability/descent auxiliary for `lem-a1-affine-hc0`, not an attempted change to the Rankin–Selberg unit statement. The current blueprint update for the already existing valuation-domination node was read: its statement allows any local subring of a field, and the proof here uses the narrower fraction-field case that both old and new statements cover. No other node is edited. There is no statement dispute or source error.

## Not duplicates

No new nodes. DAG title/concept searches identified and reused all the required nodes. Whole-blueprint searches for `valuation`, `dominat`, and `flat valuation` found the existing valuation-domination input and no second copy of this item. The blueprint ancestor tool gives `lem-a1-affine-hc0`; the item's existing precise `from.place` and `via` are preserved and `same_as` is filled with the empty list.

## Mathlib searches

All five existing item queries were run through the mandated `msearch.py NC lem-a1-flat-valuation-lifting` command and their outputs read; their actual queries and verdicts remain in `mathlib_searches` and are logged in `searches.jsonl`. The two LeanFinder phrasings returned `Flat.generalizingMap`, `Algebra.HasGoingDown.of_flat`, and valuative-criterion declarations; Loogle `AlgebraicGeometry.Flat, ValuationRing` and the algebraic-geometry grep found no match. LeanSearch returned `Flat.isStableUnderBaseChange`, formally smooth lifting, valuation-extension classes, and a generalizing-map result. None gives the requested compatible extension and scheme map in one specialization. I read `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` (base-change instances and stalk criterion) and `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` (the Existence definition) to distinguish these claims. No unavailable service is reported as an absence.

## Review by NC

I read Stacks 089F in `spaces-morphisms.tex` and the definition of extensions of valuation rings in `more-algebra.tex`. The item allows arbitrary flat scheme morphisms and arbitrary valuation rings; the source also has no finite-presentation, Noetherian, rank, or discreteness assumption. Each cited node's statement was opened before writing its use, and every quote in `citations.json` is copied verbatim from that statement. I checked B–E against the written split, as follows.

Step 1 uses exactly the fraction-field valuation condition in `def-trf-valuation-ring`. The argument that nonunits form an ideal is written out: total divisibility compares two nonzero nonunits, while multiplication cannot turn a nonunit into a unit. The zero cases are immediate. This is an elementary deduction, not a new lemma node. The domain condition also ensures zero is a prime ideal in step 4.

Step 2 uses `def-pc-fibre-product` for the projections and their commuting identity. `lem-weil-common-extension-fields-tensor-nontrivial` really says the tensor of the two residue-field extensions is nontrivial; `lem-weil-common-extension-fields-maximal-ideal` really supplies a maximal prime of any nontrivial commutative ring; `lem-weil-pbc-fibre-product-points` identifies the quadruple with a point having exactly the required two projections. Its two field extensions are over the same residue field of t, because f(y)=b(s). This explicitly repairs the potential hidden inference that a point over the closed point automatically remains a point after base change. I also read Stacks 01JT, `schemes.tex`, `lemma-points-fibre-product`, for this use.

Step 3 uses `lem-weil-pbc-flat-morphism-base-change`, whose assertion allows an arbitrary base morphism, to make h flat. I read Stacks 01U9, `morphisms.tex`, `lemma-base-change-flat`. `def-weil-flat-morphism` supplies precisely flatness and locality of the stalk map. Part (a) of `lem-weil-pbc-morphism-from-spec-local-ring` supplies the necessary germ isomorphism with R. No assertion that a globally flat morphism is surjective is used. Flatness is simply transported along this ring isomorphism.

Step 4 applies `lem-weil-pbc-flat-faithfully-flat-maximal-ideals` only after checking its proper-extended-maximal-ideal condition: locality puts m_R B inside m_B, and R has just one maximal ideal. `lem-weil-pbc-faithfully-flat-surjective-spectrum` then supplies an actual prime over zero, not just an injectivity statement. I read the source 00HQ (`algebra.tex`, `lemma-ff-rings`) and the immediately following `lemma-local-flat-ff`, as well as the statement of the maximal-ideal criterion. This follows the source's faithful-flatness route instead of substituting a different geometric criterion.

Step 5 first checks both hypotheses on A=B/q: it is a domain because q is prime, and it is local because every element outside n/q comes from a unit in B. Then `lemma-nagata-local-domain-valuation-dominates` really gives the valuation overring and maximal-ideal contraction. I read Stacks 00IA (`algebra.tex`, `lemma-dominate`) and the current main-20261015 blueprint file for that node. The old DAG sentence and updated blueprint both apply with L=Frac(A); no stronger conclusion from the node's proof is borrowed. This existing Lean-closed tool is also declared in `split_report.tool_uses` for clarity.

Step 6 separately verifies the two requirements that could otherwise be conflated: the contraction q∩R=0 proves injectivity; the two contractions of maximal ideals prove locality. Part (b) of `lem-weil-pbc-morphism-from-spec-local-ring`, read also in Stacks 01J6 (`schemes.tex`, `lemma-morphism-from-spec-local-ring`), constructs d and identifies the two resulting maps by the actual point/local-hom bijection. Its part (a) controls the germ identification. `def-weil-affine-spectrum` supplies the morphism induced by iota and `def-pc-fibre-product` supplies f p=b h. Thus the final square follows from equality of explicitly computed local maps and composition. This step is elementary after those cited correspondences; it does not silently assume a topological factorization is a scheme factorization.

Small cases: if R is a field, m_R=0, the faithful-flat criterion still applies because B is a nonzero local ring, and q lies over zero as required. If R has arbitrarily high rank, the argument still uses its single maximal ideal and its zero prime only. B need not be reduced or a domain: quotienting by q is essential and was kept. A zero target fibre cannot satisfy the image hypothesis, so it is not accidentally admitted. A non-rational closed-fibre point is allowed: the tensor and maximal-ideal argument explicitly handles the residue-field extension. No non-elementary step is over 2000 characters, and no fact is hidden in a new restatement node.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own independent stage states; no Lean files were written and no compiler or build command was run. Server dry-run validation and direct push are performed with the prescribed delivery command.
