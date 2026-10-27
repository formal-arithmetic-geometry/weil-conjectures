# Worker report: lem-sfb-space-relative-ample-locus

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-ample-locus.json`: existing statement, split into nine steps; assertion unchanged; statement dependencies now name the canonical ringed-topos and Zariski/etale interpretations of its pullbacks.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-noetherian-approximation.json`: statement, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-limits-schematic-stages.json`: statement, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-invertible-limit-descent.json`: statement, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-noetherian-ample-neighbourhood.json`: statement, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-ampleness-fpqc-descent.json`: statement, no Mathlib match.

`citations.json` contains the verbatim supporting quotation for every node in every proof step. `search-results.json` retains the actual search responses, and `searches.jsonl` is the search command's unmodified log. No Lean was written and no compiler or build was run.

## Attachments

None. Searches for the exact blueprint tag and ampleness-locus terminology under `lean/WeilConjectures/` found no declaration covering the algebraic-space assertion. The scheme `IsAmple` definitions, Chow relative-ampleness results, and very-ampleness field-descent declaration do not state this item. In particular, scheme-only declarations cannot establish schematicity of a general algebraic space.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## What required attention

The item had no proof. I followed the scheme-base paragraphs of Stacks 0D3D, including the argument labelled (A), rather than using 0D3D itself as an unsplit replacement node. No statement dispute or change of mathematical meaning was needed. The existing provenance has `blueprint.from.node = null`; `blueprint_refs.py ancestor` confirms None. I retained this provenance and made each new node's supporting place explicit in the same chain. This is an auxiliary ampleness input for the canonical-line step of `lem-sfb-stable-and-smooth-family-open-loci`, serving the specified moduli/alteration route below the constructible-finite-Tor stability unit. I did not change the chapter, unit, targets, or route.

Two gaps would have resulted from treating existing scheme results as algebraic-space results. The available etale descent node does not descend along an arbitrary residue-field extension, and the available line-bundle limit descent and eventual-affine-stage results assume scheme stages. These gaps account for genuine supporting space lemmas. The Noetherian neighbourhood lemma is only the Noetherian spreading input, not the arbitrary-base universal open theorem: the item's proof performs approximation, fibre descent, affine pullback, construction of the open, and its functorial characterization.

The proper approximation is an inverse limit of arrows with affine transitions; its squares are not assumed cartesian. I used the affine projection to the schematic Noetherian neighbourhood directly to pull back absolute ampleness. I checked the Stacks tag index and corrected the auxiliary reference for the hypotheses of invertible descent to 07SK. I added explicit citations for the integer-base Noetherian result, the qcqs affine base, and the affine scheme tests/base changes, instead of hiding them in the spreading argument.

## Not duplicates

lem-sfb-space-invertible-limit-descent vs lem-sfb-fp-space-limit-category: the existing 07SK statement descends finitely presented algebraic spaces and their morphisms over an inverse system of affine scheme bases; the new 0D2X statement descends a line module on a limit with potentially non-schematic space stages, not an object of FP(T).

lem-sfb-space-noetherian-ample-neighbourhood vs lem-sfb-space-relative-ample-locus: the new 0D3A input assumes a Noetherian base and addresses only spreading from a specified schematic residue fibre; it neither constructs the universal ample-locus open for arbitrary bases nor gives its geometric-fibre or base-change characterization. Steps 3--9 carry the approximation, descent, pullback and universal-open arguments beyond this input; this is a strict source prerequisite, not a restated clause.

lem-sfb-space-noetherian-ample-neighbourhood vs lem-trf-algebraic-space-ample-local: the existing node descends relative ampleness along an etale cover; the new node spreads ampleness from a single fibre over a Noetherian base. A residue-field inclusion is not such an etale cover.

lem-sfb-space-relative-ampleness-fpqc-descent vs lem-sfb-space-relative-ample-locus: the new node is a cover-descent equivalence for a given line, without a proper family or a representing open; it does not spread from a fibre or construct the locus. It is used before the open can be constructed.

lem-sfb-space-relative-ampleness-fpqc-descent vs def-trf-polarized-scheme-etale-descent-datum: the existing definition specifies scheme/line cocycles for an etale cover and explicitly asserts no effective descent; the new theorem is the fpqc relative-ampleness equivalence for a given algebraic space and line.

lem-sfb-space-relative-ampleness-fpqc-descent vs lem-trf-polarized-fine-log-etale-descent: the existing theorem constructs a fine log scheme from strict etale descent data and ample lines; it does not test relative ampleness on a given space after a general fpqc cover, including inseparable field extensions.

lem-sfb-space-relative-ampleness-fpqc-descent vs lem-trf-algebraic-space-ample-local: the latter assumes a jointly surjective etale family from schemes, while the new node allows fpqc coverings; inseparable field extensions needed in step 2 need not be etale.

lem-sfb-space-relative-ampleness-fpqc-descent vs lem-trf-polarized-scheme-etale-descent: the latter constructs a descended pair from an etale descent datum; the new node tests relative ampleness of a given line on a given algebraic space after fpqc pullback.

lem-sfb-space-invertible-limit-descent vs lem-trf-invertible-affine-limit-descent: the existing node requires every stage and limit to be schemes; the new node allows algebraic spaces with line modules on their etale sites.

lem-sfb-space-noetherian-ample-neighbourhood vs lem-trf-noetherian-fibre-ample-neighbourhood: the existing node assumes the total space is a scheme; the new node must establish schematicity over the open as part of relative ampleness.

lem-sfb-space-noetherian-ample-neighbourhood vs lem-trf-ample-neighbourhood: the latter permits arbitrary base schemes but assumes a scheme source throughout; neither removes the algebraic-space schematicity issue handled by 0D3A.

lem-sfb-space-proper-noetherian-approximation vs lem-weil-pbc-proper-limit-noetherian: the existing node approximates a proper morphism of schemes, while the new node applies before the source or its finite stages are schemes.

lem-sfb-space-affine-limits-schematic-stages vs lem-weil-pbc-limit-affine-transition: the latter is about limits of schemes; the new node permits non-schematic stages and includes eventual schematicity/affineness. Its clauses are the closely related space-limit and representability-detection facts 07SF/07SQ/07SR, not a new ampleness assertion.

## Searches and scope

Before creating nodes I searched the whole DAG by Stacks tags 0A0X, 07SF, 07SQ, 07SR, 0D2X, 0D3A, and 0D3C, and by ampleness, line descent, and inverse-limit terminology. I used `blueprint_refs.py search` for the tags and the concepts `ample neighbourhood`, `ample invertible`, `relatively ample`, `algebraic space`, `inverse limit`, `invertible module`, and `Noetherian approximation`. None states these space results. Existing scheme ampleness/limit results are cited rather than duplicated. All Mathlib queries were run through the required `msearch.py` command with the actual queries recorded in each node; two semantic phrasings were tried per proposed node and per item, plus Loogle, grep and LeanSearch.

The relevant Mathlib hits `AlgebraicGeometry.isAffineHom_π_app` (AffineTransitionLimit.lean:363) and `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` (same file:1040) were read in source. Their diagram objects are schemes, so they do not state the new algebraic-space inverse-limit node. Other hits concern proper scheme morphisms, general descent of morphism properties, or descent of sections; they do not provide these space/line results. There are zero Mathlib leaves. The item's inherited searches remain intact and are supplemented with the searches of this session.

## Review by O3

I read `spaces-descent.tex`, lemma-ample-in-neighbourhood (0D3D), especially all paragraphs of (A), and `spaces-divisors.tex`, definition-relatively-ample (0D31), its scheme-base sanity check (0D32), base change (0D33), and lemma-ample-in-neighbourhood (0D3A). For each new node I read its own source: proper approximation 0A0X; limit existence/affine projections 07SF and the detection lemmas 07SQ/07SR with their qcqs Situation 084R; invertible descent 0D2X with the hypotheses of lemma-descend-finite-presentation 07SK; Noetherian fibre spreading 0D3A; and the entire fpqc statement and proof of descending-property-ample 0D3C. The five new nodes have self-contained statements and no proof sketches or proof dependencies.

Step 1 uses the ringed etale model node for arbitrary morphisms and the Zariski/etale quasi-coherent equivalence node for its explicit invertible-module and tensor-pullback comparisons. I opened both statements; they give those assertions, rather than only defining a restriction functor. Local rank-one freeness persists by pulling back the trivializations and their inverses.

Step 2 uses the field-extension fpqc-cover statement and the new fpqc ampleness equivalence. Their hypotheses apply to the actual field extension K/kappa(t), including inseparable and transcendental extensions; the equivalence includes schematicity of the residue fibre. Scheme relative-ampleness base change gives the converse. No etale claim is used for an arbitrary field extension.

Step 3 uses the affine-basis statement and the affine-scheme qcqs statement to obtain exactly the base required by proper approximation. The approximation node has affine transitions on both sides. The affine-limit node is applied to its base tower, with affine limit T and qcqs stages, to make the finite-stage bases affine; its affine-projection clause applies separately to the source tower. The restriction of properness is explained from the defining conditions. I did not apply a scheme-only approximation theorem to X.

Step 4 uses precisely the new line-module descent statement, with qcqs space stages and affine transitions verified in step 3. Later line modules are actual tensor pullbacks of the chosen one. No object is chosen from an unspecified existence theorem and then assigned properties absent from that theorem.

Step 5 uses the existing residue-field colimit statement only after the bases have become schemes, so its hypotheses hold. Commutation of limits with fibre products is written as the equality of test-scheme tuples; it is a formal limit argument, not a cited theorem about scheme stages. Affine morphisms from affine scheme tests and affine base change give the fibre transitions. Proper fibres of the finite-presentation approximants are qcqs. The space-limit node supplies schematicity of the fibre stages before the scheme-only 09MT ampleness-descent node is invoked. The latter's statement gives exactly the eventual ampleness required; it is not being used for its internal construction or for non-schematic stages.

Step 6 first cites the existing finite-type-over-Noetherian statement, which explicitly includes finite-type schemes over Spec Z. Thus 0D3A is applied to a proper space over a genuinely Noetherian scheme and an already schematic ample fibre. After shrinking to an affine V_i, relative ampleness gives absolute ampleness on X_{i,V_i}. The affine projection X -> X_i makes its inverse image X_V a scheme. The affine pullback lemma applies to the actual scheme morphism X_V -> X_{i,V_i}; the same lemma and the affine-scheme/permanence nodes handle every affine open W of V. This replaces the temptation to assume the approximation square is cartesian.

Step 7 uses scheme relative-ampleness base change for the fibre condition and the existing algebraic-space ample-local node for both schematicity and ampleness after gluing. Its statement really includes both conclusions and allows a jointly surjective family of etale scheme maps, so it applies to the open cover of A even when A is not quasi-compact. The proof does not infer absolute ampleness from an arbitrary open cover of X; it descends relative ampleness over a cover of the base.

Step 8 again uses exactly scheme ampleness base change, the field-cover criterion, and the new fpqc equivalence. For the reverse implication the relevant extension is kappa(t')/kappa(t), not a supposed equality of the two residue fields. This proves image containment in the open A, and factorization through an open subscheme is the direct restriction of the morphism and its sheaf map. Step 9 is elementary: substitute the universal property into the pullback square, and test inclusions of two putative representing opens. This proves arbitrary base-change compatibility and includes X_A being a scheme. No non-elementary comparison is hidden in this step.

For small cases I checked the empty total space (every line is ample and A=T), empty base and empty A, and a family over a field (the locus is either all or empty, with fpqc descent detecting the same choice over every field extension). A non-schematic proper space with no ample geometric fibre simply has empty locus, so no global schematicity is inferred. Constant families with L=O(-1) on P^1 give empty locus, while O(1) gives the whole base; the statement is not vacuous. For the limit-detection node, a schematic limit alone does not make every stage a scheme: the conclusion is correctly eventual, with qcqs stages essential. For invertible descent the system is small, directed and nonempty and no fixed prechosen stage is promised. The fpqc statement assumes no properness, whereas the Noetherian spreading statement retains properness. These distinctions keep the new nodes strictly smaller than the universal-locus item.

I checked delivery-errors B--E: the source tags agree with the local tag index; no new node duplicates an existing scheme statement or restates the universal-locus conclusion; every non-elementary step has statement-level citations; no forbidden SGA reference is used; no argument step exceeds 2000 characters; and no item or new node cites a descendant that could form a cycle. Existing off-unit generic tools are explicitly declared in `split_report.tool_uses`. Every quote in `citations.json` was checked as a verbatim substring of the cited node's actual statement. The mandatory server dry run passed; its receipt is recorded below.

### Repair reading after the landing refusal

I compared the retained item with returned commit `5cf5d7ff3e4b12935d025a42d888295e15ed7dc1`: it was exactly the returned node before this repair. I then compared every existing statement/proof dependency between that head and the current `0082fa1862570a193d02f4821b4e5f6119073c93`, reading Git objects directly without running Git or writing in the read clone. `return-comparison.json` preserves that comparison. Only `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` changed: its proof, proof dependencies, proof origin, split report and review changed; its statement did not. All other existing cited nodes were unchanged. The current item's statement and maintainer-owned fields agree with the retained copy; the live item remains unsplit and the five auxiliary nodes remain absent.

I re-read the changed comparison node, including its four-step assembly and its maintainer review. Its new step 2 obtains the rank-one comparison from the existing invertible-comparison node, while step 3 still proves the canonical tensor-pullback comparison for arbitrary scheme morphisms. Consequently our step 1 needs no new hypothesis and no replacement dependency. I added an explicit sentence distinguishing that unrestricted pullback assertion from the quasi-compact separated direct-image assertion, which this delivery does not use. I also expanded step 5 into the actual compatible pairs of test-scheme maps proving the fibre-limit identification; no cartesianity of the approximation squares is assumed. Step 8 now uses ordinary prime notation in TeX. These are changes to the retained split, rather than an unchanged re-push.

For the requested repair I re-opened the item source 0D3D, fpqc descent 0D3C, Noetherian spreading 0D3A and the five supporting limit-source statements. Their hypotheses remain those checked above. All 26 step-citation quotations remain verbatim in the current statements and cover exactly the cited pairs. The longest repaired step is still below 2000 characters. The existing searches and full responses were read and retained: the statement/search questions have not changed, so no search was repeated or invented. The initial required dry run on the retained split exited 0 with `OK (not pushed)` at `a63757c6220`; a further dry run checks this repaired proof and report before pushing. Promotion of the old side completion is the maintainer's action; this delivery supplies the current-base repaired branch without setting any completion or review field itself.

## Unfinished work

No mathematical step left unfinished. The five auxiliary nodes are intentionally statement-only and unsplit, as required for a one-level split. The required server checks passed before delivery.

## Validation

The required `deliver.py O3 lem-sfb-space-relative-ample-locus --no-push` exited 0 and printed `OK (not pushed)` at e77635dd717, with server preflight passed. Earlier diagnostic runs required additional same-tag statement comparisons and a fuller quotation of the affine ample-pullback lemma; both were repaired. The final dry run completed before the push invocation. There are five new unsplit statement nodes, zero Mathlib leaves, and no Lean or build changes.

## Return repair validation

The landing return at 2026-10-22 07:09 UTC requested rebasing onto the current DAG and re-reading changed citations. The comparison and repair above discharge both requests. The delivery tool builds the repaired commit on the current server DAG and preserves its maintainer-owned fields. Final dry-run and push results are reported by the delivery command; the earlier Validation paragraph is the retained history of the first delivery.

### Resumed repair verification (2026-10-22)

After the provider interruption I checked that no delivery invocation was active before starting the required dry run. That run exited 0 and printed `OK (not pushed)` at `d376591ea43`. I then refreshed `return-comparison.json` against the current DAG `eef7b48e43488e923f0bb841e49e7ec93ac4d073`, comparing the original returned head `5cf5d7ff3e4b12935d025a42d888295e15ed7dc1`. The item still differs from the returned version in its proof and split report; its statement is unchanged. The only changed cited node remains `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`, with unchanged statement. I read its full current four-step proof and maintainer review again: the replacement rank-one comparison is obtained from the existing invertible-comparison node, and the pullback comparison still applies to arbitrary scheme morphisms. Our step 1 uses exactly those two assertions and imposes no direct-image hypotheses.

I also reread all the item proof steps and the statements of every cited node, rechecked all 26 quotation entries against the current statements, and reopened 0D3D, 0D3C, 0D3A, 0D31, 0A0X, 07SF, 07SQ, 07SR, 084R, 0D2X and 07SK in their local source files. In particular, eventual schematicity is used before the scheme-only ample-limit result, and the affine projection in step 6 suffices without cartesian approximation squares. The five supporting statements remain absent from the current DAG. The recorded Mathlib results have been read and retained because no statement or search question changed. The attachment search in the current project library found no declaration of the item. The longest proof step has 1255 characters; none needs the long-step review. This updated report is checked by the final dry run before the push.

### Current-base repair verification (2026-10-23)

The mandatory first dry run of the retained split completed successfully at `f799b1c35d1` before I changed anything. I refreshed `return-comparison.json`: the original returned head is `5cf5d7ff3e4b12935d025a42d888295e15ed7dc1`, and the current DAG examined is `b6490c2d7b206cfd684a16938a6bfe333336c7e2`. Every existing statement/proof dependency was compared. The sole changed dependency remains `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`; its statement is unchanged. I read its four current proof steps and full maintainer review. Its rank-one equivalence still identifies the given line, and its arbitrary-morphism tensor-pullback comparison still identifies every pullback used here. The separated quasi-compact direct-image clause is unused. The live item is unsplit; none of the five supporting nodes exists in the live DAG. Thus this delivery promotes the retained side split on the current base, rather than treating its earlier side completion as a live completion.

I re-read all nine proof steps, the statements of all their cited nodes, and the local source statements/proofs 0D3D, 0D3C, 0D31/0D32, 0D3A, 0A0X, 07SF, 07SQ, 07SR, 084R, 0D2X and 07SK. The small-case checks recorded above still apply. Step 5 now writes the actual affine tests E and F for the transition between fibres: both are affine over the same affine test of X_i; their map and its affine-test pullbacks are affine by the two cited scheme statements. This explicitly justifies the space-affineness definition before eventual schematicity is invoked. It uses no cartesian approximation square and creates no new sublemma. Every step remains under 2000 characters. The repaired proof and updated split report differ from the returned head; the mathematical statements are preserved.

I checked every one of the 26 quotation entries against the current cited statements and checked exact coverage of all step/node pairs. All quotes remain verbatim. I retained and read the existing Mathlib searches and their responses: their queries and the statements are unchanged, so none was rerun or invented. I repeated the project-library attachment search, which found no complete declaration of this item. The final server dry run below checks the revised proof and report before the sole push invocation. No review/completion field, repository file, launcher script, Lean source or build artifact was written by this worker.
