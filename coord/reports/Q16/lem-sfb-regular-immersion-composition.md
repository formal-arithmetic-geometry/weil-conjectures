## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-immersion-composition.json`: statement, now split into five steps; no statement change. The item is not a Mathlib leaf.
- No new nodes, hence no new Mathlib leaves. All supporting statements already exist in the DAG. `citations.json` contains seven citations, each with a verbatim copy of the cited statement. `searches.jsonl` preserves the actual search-command records.

## Attachments

None. `AlgebraicGeometry.IsRegularImmersion.comp` in `lean/WeilConjectures/AlgebraicGeometry/Morphisms/RegularImmersion.lean:532` is a project declaration, but its class extends closed immersion and fixes a global codimension. Its statement does not cover arbitrary, possibly nonclosed immersions with locally varying sequence lengths. No declaration bearing this item's blueprint tag was found. The project theorem is therefore not an attachment. Ordinary `AlgebraicGeometry.IsImmersion.comp` is in Mathlib, not a project attachment.

## WANTED

None. All sources used are available in the read clone.

## Findings and changes

The imported statement is correct as written: it explicitly defines regular immersion using local affine charts and allows the empty sequence. I read divisors.tex, Tag 067Q, `lemma-composition-regular-immersion`, assertion (1), together with Tags 063J (`definition-regular-immersion`) and 063G (`lemma-regular-ideal-sheaf-scheme`). The source imposes no Noetherian hypothesis. The algebraic input is algebra.tex, Tag 065K, `lemma-join-regular-sequences`, whose proof explicitly says it follows immediately from the definitions. That argument is written out in step 5, rather than exported as a new node.

The missing geometric detail in the short Stacks proof is choosing compatible affine charts. Step 3 writes out the proof of schemes.tex, Tag 01IW, `lemma-standard-open-two-affines`, using two existing principal-open statements. In particular the intersection of the original affine opens is never assumed affine. Choosing first D(h) in one chart and then D(b) in the other, and expressing the restricted b as c/h^N, gives the common principal open D(hc). This is a few-line consequence of the cited basis and section statements, not an additional unsplit lemma.

I searched the whole DAG by 067Q, 063G, 063J, 02V0, 01IW, regular sequences, localization, and immersion composition; the blueprint search command was run for regular immersion, regular sequence, concatenation, composition of immersions, immersions compose, 02V0, and 01IW. Some returned unrelated scalar-functor composition nodes. No blueprint node states this arbitrary-scheme regular-immersion composition result; the Noetherian geometric-calculus node `lem-per-regular-lci-geometric-calculus` has stronger hypotheses. The inherited `blueprint.from.place` identifies the Tag 067Q input to Tag 0570, itself supporting the ctf-stability alteration route. The ancestor command returns None for this inherited chain; its null ancestor and via list were preserved, with `same_as: []`. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, the recorded unit and chapter, GOAL.md, SETUP.md's three levels, and the delivery-error checklist B–E. No chapter or unit route is changed.

Mathlib searches were run using msearch.py only, with actual results read and recorded. The semantic searches return ordinary IsImmersion.comp and algebraic sequence operations. The regular-immersion name search returns no Mathlib declaration. The ordinary immersion composition search finds IsImmersion.comp at Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:146–148, and the factorization interpretation is at lines 155–158. The weak regularity searches find IsWeaklyRegular.of_isLocalization at Regular/Flat.lean:59–61 and the more general flat results at lines 34–49, read with their variables. These support existing leaves; they do not prove the item's geometric conclusion in one line. I initially considered creating an ordinary immersion composition leaf, then found clause (e) of `lem-weil-pbc-proper-fp-permanence`; it already states the needed fact, so no node was created. The existing localization leaf was likewise reused. Earlier searches already recorded in the imported item are retained.

## Review by Q16

I checked the mathematical split with the node statements and the Stacks sources open. This is the author's direct-delivery self-review, for the maintainer's independent review.

Step 1 uses exactly the immersion clause of (e) in `lem-weil-pbc-proper-fp-permanence`. Its opening quantifies arbitrary scheme morphisms; properness and finite-presentation assumptions occur only in other clauses. Thus no such hypothesis is imported into the immersion assertion. The current Mathlib composition instance and the factorization lemma confirm the meaning of immersion. This existing Mathlib leaf is a generic tool, so using it does not replace the unit route.

Step 2 only unpacks the two hypotheses at z and i(z). It does not assume either local source chart is the whole inverse image of its ambient affine chart. That distinction matters because the item's chart definition only specifies an open neighbourhood in the source. All subsequent constructions stay inside those chosen source charts.

Step 3 uses the basis clause (i) of `lem-weil-pbc-spec-localization-away-basic-open` twice, and clause (b) of `lem-weil-pbc-affine-open-section-vanishing-prime` for the section ring on D(h). Both cited statements apply to arbitrary rings and schemes. The fraction c/h^N is defined on D(h), where h is invertible. Its nonvanishing locus there is D(hc) in the original first chart. This is the explicit two-chart refinement in Tag 01IW. Surjectivity of A to A/I supplies the lift a; no lifting across a nonsurjective map is used.

Step 4 uses the principal-open section clause of `lem-weil-pbc-affine-open-section-vanishing-prime` on the ambient charts and on the affine chart Z_0, and clause (1) of `lem-weil-pbc-closed-immersion-affine-cover-criterion` for the closed morphism Z_0 to W. The cited criterion actually gives affine inverse images and surjective section maps; a definition node alone would not supply this. The quotient/localization isomorphism is given explicitly by fractions, so no unmentioned quotient comparison is used. `lem-exc-weakly-regular-sequence-localization` supplies precisely the injectivity conditions for the f and g sequences after localization, without asserting a nonzero final quotient. This is why the argument does not claim that every localization preserves regularity in the stronger sense.

Step 5 uses only the definition in `def-weil-pbc-regular-sequence`. It calculates the composite kernel by lifting finitely many coefficients and identifies each tail prefix quotient with the corresponding prefix quotient over R'. That proves every required multiplication injective. It separately verifies the nonzero final quotient from the retained point z. The step proves concatenation itself and does not merely invoke an unnamed join lemma. This avoids C1, C4, and D1/D2: no source citation is substituted for a needed fact, every non-elementary input is already a cited statement, and none of the item's substance is moved into a replacement node.

For section E I tested both zero-length blocks, both identity immersions, nonclosed open immersions, and the empty source. With an empty first block the quotient comparison is the identity; with an empty second block the tail argument is vacuous. The empty total block gives the identity chart. A nonempty source point ensures C is nonzero even though localization may annihilate a ring away from that point. For empty Z the pointwise condition is vacuous but step 1 still establishes the immersion. The proof does not use permutation of regular sequences, Noetherianity, flatness of i or j, or affineness of an intersection. These checks required no statement correction. There are no new statements needing separate edge-case tests, and every proof step is shorter than 2000 characters.

## Not duplicates

No new nodes were created. Ordinary immersion composition, principal neighbourhoods, affine section localization, the closed-immersion affine criterion, and weak regularity localization are all supplied by existing nodes. The elementary sequence-joining and finite coefficient-lifting arguments remain in the proof.

## Unfinished work

None in the requested stage-1 split. No Lean file was written and no compiler, Lake, or build command was run. Server dry run and delivery results are recorded below after the commands complete.

## Validation

The required server dry run exited 0 and printed `OK (not pushed) deliver/Q16/lem-sfb-regular-immersion-composition at d0d211e68d6: preflight passed`. This includes the maintainer's stage-1 preflight, DAG and split checks. No local copy of those checkers was run.
