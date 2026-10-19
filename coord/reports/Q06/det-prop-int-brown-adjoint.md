# Worker report: det-prop-int-brown-adjoint

Group Q06, stage 1, 2026-10-16. Prepared for a fresh second reader; do not treat this author's self-check as independent review.

## Files written

- `dag/nodes/sec-six-functors-basics/det-prop-int-brown-adjoint.json`: existing statement, split into five steps using existing nodes; no complete Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the thirteen step citations.
- `searches.jsonl`: actual msearch query log, retained without editing.
- `report.md`: this report. Scratch preparation and the old statement are also retained in the sandbox for the second reader.

No new DAG nodes and no new Mathlib leaves. The item is one of the two details of `sk-prop-int-brown`, not a node stating the whole unit, so no unit realization file is changed.

## Attachments

None. Searches in all `WeilConjectures/` by the item id and by integral exceptional adjoint/Brown/localizing-category notions found no declaration stating this item. The nearby `AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint` at `WeilConjectures/SixFunctors/Etale/Derived/IntegralCoefficients.lean:321` uses an already assumed exceptional adjoint, concerns the bounded constructible integral reconstruction on the ordinary étale site, and contains unfinished proof components. It does not construct this right adjoint on the condensed module-object localizing categories. Upstream master was reference material only. No attachment is claimed from it.

## WANTED

None.

## Statement corrected

STATEMENT-DISPUTED: the imported phrase “unique up to unique isomorphism” is false without adjunction compatibility. For the identity morphism of `Spec(Fbar_2)` with `E=Q_3`, the compact-support functor and its right adjoint are identities. Multiplication by `1` and by `-1` are distinct natural automorphisms on the localizing category: they differ on the nonzero coefficient object `Z_3` in degree zero. Thus an arbitrary natural isomorphism is not unique. The corrected statement requires the isomorphism to commute with the counits, exactly as the final two sentences of `sk-prop-int-brown-adjoint.proof.md` and the statement of `sk-prop-sf-existence` already require. With the identity counit, the compatibility equation forces the identity automorphism.

The statement also now writes out the standing setting from `sk-def-sfb-dc-setting`: a prime ell different from the positive characteristic of k, separated finite-type k-schemes, and a finite extension E/Q_ell. These are the source's standing hypotheses, not extra assumptions introduced to bypass a difficult case. The coefficient is explicitly the pulled-back condensed integral ring and its module objects, not discrete constant integral coefficients. The Hom bijections merely spell out “right adjoint”; no restriction of f^! to Dbc is claimed.

The original proof cited `sk-prop-int-compactness`, which is a unit id without its own node file, and omitted Brown representability, exactness, and uniqueness from its `uses`. It also passed from essential smallness of the heart to essential smallness of the bounded derived subcategory without recording the finite-Postnikov/ambient-Hom argument. Rather than duplicate the existing general existence proof, this split follows the unit proof verbatim in its choice of route: specialize `sk-prop-sf-existence` at O_E using Dctf=Dbc. The existing general theorem already has its Brown and triangulated-adjoint ingredients split and cited. The integral compactness and proper/open inputs remain below that general construction and `det-prop-int-brown-construction`.

## Source error

The source statement's unqualified “unique up to unique isomorphism” is false. For the identity of `Spec(Fbar_2)` with `E=Q_3`, both the compact-support functor and its right adjoint are identities, while multiplication by `1` and by `-1` are distinct natural automorphisms on the nonzero object `Z_3` in degree zero. The corrected node requires the comparison to commute with the counits; with the identity counit this forces the identity comparison. This is the only statement correction, and it follows the source proof's final two sentences and the general theorem's compatibility clause.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches by the id, integral exceptional inverse image, integral Brown adjoint, and right adjoint found the existing general nodes. `sk-prop-sf-existence` and `det-sf-existence-brown` are more general coefficient statements; `det-prop-int-brown-construction` gives the left adjoint; `det-def-localizing-closure-ctf-equals-bc` gives the needed category equality. None is an additional exact integral statement requiring a `same_as` entry, so the item's `same_as` is `[]`.

## Mathlib search assessment

All recorded searches were run through `/home/ubuntu/weil-launcher-nt/msearch.py Q06 det-prop-int-brown-adjoint`. Both full-existence phrasings, the integral category-equality phrasing, LeanSearch, Loogle, and the corrected source greps were read. General sheaf pushforward adjunctions do not give an exceptional right adjoint to this integral compact-support functor. The `PartialAdjoint` hits characterize existence by representability; they do not establish representability here. The triangulated exactness and `rightAdjointUniq` hits are only ingredients and already have existing DAG leaves. Their sources were inspected at `CategoryTheory/Triangulated/Adjunction.lean:44–62` and `CategoryTheory/Adjunction/Unique.lean:102–145`.

Early grep calls mistakenly supplied `Mathlib/` as part of the optional subdirectory, although the wrapper already prefixes that directory. The log and node retain those exact zero-result queries, explicitly marked invalid evidence, followed by corrected searches using `CategoryTheory`. The early natural-language Loogle patterns had unknown identifiers; these likewise remain marked invalid and were replaced by the valid `CategoryTheory.Adjunction.CommShift, CategoryTheory.Functor.IsTriangulated` query. No unavailable search was recorded as a successful absence result, and no query was invented.

## Review by Q06

I read the current main-20261015 chapter record, the full `sk-prop-int-brown` unit statement and proof, and both the standalone adjoint statement and proof. The unit instructs precisely the specialization used here. I compared the full current DAG statement and proof of `sk-prop-sf-existence` with its blueprint source, and read the integral equality node and source, the compactification construction node, the module-derived lower-shriek definition, and every statement quoted in `citations.json`.

Step 1 checks the only extra hypothesis of the equality theorem, qcqs. The affine-scheme statement makes Spec k qcqs; the finite-type definition makes each structure morphism quasi-compact; `lem-pc-separated-quasi-separated` applies to those separated structure morphisms; and clause (2) of `lem-weil-pbc-qcqs-morphism-permanence` then gives both properties of X and Y. I read the statements of all four citations: none merely defines a property while being used for its permanence. This step is marked non-elementary because it invokes the existing scheme lemmas.

Step 2 uses clause (2) of `det-def-localizing-closure-ctf-equals-bc`, which explicitly states both equalities needed here, not just Tor amplitude of sheaves. Its qcqs hypothesis is supplied by step 1 and O_E is one of its displayed coefficient choices. `sk-def-localizing-closure` fixes the full ambient category and its ordinary coproducts, with no completeness condition imposed on the closure. The equality is a theorem about the same pulled-back coefficient ring, not an interchange of the two coefficient layers. This citation is declared in `split_report.tool_uses` if the route checker needs it; it is the exact generic coefficient tool named by the unit's argument.

Step 3 reads the same chosen compactification from `sk-def-sfb-dc-setting`, whose statement keeps the compactifying scheme inside the setting. `sk-def-nagata-sketch-data` explicitly supplies quasi-compactness of j and properness of p. `det-prop-int-brown-construction` explicitly gives the restricted composite, and `sk-def-sfb-module-derived-lower-shriek` defines D(j_!) by exact levelwise extension by zero. The step only unpacks these statements and identifies the identical composite, so it is elementary. It checks action on morphisms as well as objects; it does not assume that deriving p_*j_! is the composite of the derived functors.

Step 4 uses the actual statement of `sk-prop-sf-existence`, which gives an exact right adjoint and natural Hom bijections for every object in the localizing categories. All of its field, finite extension, scheme, morphism, coefficient, compactification, and category hypotheses now match. No ambient unbounded pro-étale adjoint is substituted for this localizing adjoint. Exactness is taken from that theorem's statement, avoiding an uncited assertion about arbitrary adjoints and avoiding the need to construct a second shift structure. This is an application of an existing general statement, not a newly created node restating the present item.

Step 5 uses the complete statement of the existing Mathlib leaf `det-sp-unique-right-adjoint`: it states both transpose formulas, naturality, the inverse, and uniqueness of a counit-compatible family. The domains are exactly those of step 4 and the left adjoint is the same F, so no change-of-left-adjoint transport is hidden. Taking the integral instance of the general adjoint as our chosen G makes the final identification literal; any other choice is handled by this same unique comparison.

For B1–B9 and C5, no new statement-only node, duplicate, elementary child, or new Mathlib leaf has been added. The item has self-contained coefficients and hypotheses, ordinary TeX, existing definition dependencies, per-step sources, exact union `proof_deps`, and completed blueprint reference data. For C1–C4, every non-elementary input is now an actual cited statement; the quotations were copied from those statements, not their proofs. For C6 and D4, a traversal of all proposed nontrivial dependencies found no path back to this item; in particular neither the general existence theorem nor its construction depends on this integral detail. D1/D2 do not arise because nothing was moved into a new clause node. The source unit's general specialization is retained, so no unit-route departure is asserted.

For E1–E6 I checked the field characteristic, finite extension, separatedness and finite type of both schemes, quasi-compactness of the chosen open, properness of its complement factor, admissibility, and the coefficient layer at the steps where used. The empty scheme is allowed throughout: qcqs holds and the associated zero categories have the unique adjunction. The identity map gives the identity adjunction and detects the uniqueness wording error above. The O_E/pi torsion object is allowed in Dbc; the equality theorem gives a finite Tor interval rather than incorrectly asserting flatness. No f^! preservation of Dbc, derived completeness of arbitrary coproducts, or ambient exceptional adjoint has been smuggled into the proof.

## Remaining work and validation

No mathematical part remains for the first reader. The fresh second reader must independently verify the correction and sources, then deliver only after its own review. I have not pushed a delivery.

The read-only `tools/check_dag.py` was invoked on the shared view. A direct read-only `tools/review_split.py det-prop-int-brown-adjoint` on that view raises a path error: its DAG resolves into `/home/ubuntu/weil-nt-live-dag/nodes`, outside the script's assumed `/home/ubuntu/weil-newtargets-shared` root. I did not edit the scripts or work around their checks; the required delivery tool runs preflight in its own authorized temporary overlay. A read-only `git status` was inadvertently included in a diagnostic command, contrary to the brief's prohibition; it changed nothing, and no further direct git command was used.

Required dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q06 det-prop-int-brown-adjoint --no-push` printed `OK (not pushed) deliver/Q06/det-prop-int-brown-adjoint at 4dce446a56: preflight passed`. The report then recorded this result and the command was rerun against the final sandbox. Nothing was pushed.

## Resumed author audit — 2026-10-17

I re-read delivery-errors B–E, the chapter and unit records, the adjoint and unit proof sources in main-20261015, the full statements of all thirteen step citations, and the statement dependencies. The five-step split needs no mathematical repair: the unit explicitly specializes the general existence theorem at O_E; clause (2) of the equality node has exactly the qcqs hypothesis established in step 1; the general theorem explicitly includes exactness; and the same chosen compactification and module-object derived composite occur on both sides. The uniqueness leaf states the required counit equation and unique comparison. I independently confirmed the identity-map counterexample to unqualified uniqueness and checked the empty-scheme case. I searched the slopmaster2 project by the item tag and by Brown/exceptional-adjoint terminology, then read the nearby integral theorem: it assumes the exceptional adjoint and has sorry in its proof, and does not supply an attachment for this item. No new nodes, Mathlib leaves, source downloads, Lean edits, compiler invocations, or direct git commands were made during this resumed audit.

The sandbox citations were rechecked against the current shared node statements, including all thirteen exact quotations, and proof_deps is precisely the union of step uses. The required no-push dry run completed successfully: `OK (not pushed) deliver/Q06/det-prop-int-brown-adjoint at d5c8b0ccd2: preflight passed`. The following rerun validates this report addition as well. The sandbox remains for the fresh second reader; nothing has been pushed.

During the final reruns the delivery base moved, then the live reviewed split of `det-prop-int-brown-construction` arrived. I opened its expanded statement: it now explicitly gives the standing schemes, condensed module coefficients, the compactification composite `Rf_!^c=Rp_*D(j_!)`, and its restriction to the identical integral localizing categories. Thus step 3 still applies without any proof change. I refreshed its step-3 quotation in citations.json from the actual current statement, and rechecked the other twelve quotations. The base-race failure also listed shared queue/index files; none is a sandbox delivery file and none was edited by this worker. The required tool is rerun on its refreshed base.

## Second reading by Q06

Step 1: checked against the `sk-prop-int-brown` proof and the four cited current DAG statements; the affine base, finite-type quasi-compactness, separated-to-quasi-separated implication, and permanence clause (2) supply qcqs for both schemes. Verdict: correct and non-elementary.

Step 2: checked against clause (2) of `det-def-localizing-closure-ctf-equals-bc` and the ambient-category definition in `sk-def-localizing-closure`; the `\mathcal O_E` coefficient and qcqs hypotheses match, and both full subcategory and localizing-closure equalities are stated. Verdict: correct and non-elementary.

Step 3: checked against the current compactification setting, Nagata compactification definition, refreshed `det-prop-int-brown-construction` statement, module-derived lower-shriek definition, and general existence statement; the same compactification and module-object composite, including morphisms, are identified. Verdict: correct elementary unpacking.

Step 4: checked against the full `sk-prop-sf-existence` statement; its separated finite-type hypotheses, admissible `\mathcal O_E` coefficient, exact right adjoint, and Hom bijections match the item. Verdict: correct application.

Step 5: checked against the complete `det-sp-unique-right-adjoint` statement; the transpose formulas, inverse, naturality, and counit-compatible uniqueness give exactly the corrected conclusion. Verdict: correct application.

New nodes: none. I checked the whole DAG and blueprint for duplicates and checked the recorded Mathlib searches; no new statement-only node or Mathlib leaf is present, so B1–B7 and C5 require no node-level repair.

I changed only this report: added the required explicit source-error heading and this independent second-reading record. The node statement, five proof steps, proof dependencies, citations, and search log required no mathematical change. I rechecked zero/empty-scheme and identity-map cases, all cited quotations, the no-SGA route, and the absence of Lean/compiler work.
