# Stage-1 worker report: lem-coef-arrow-target-cartesian-pullbacks

## Files written

- `dag/nodes/sec-six-functors/lem-coef-arrow-target-cartesian-pullbacks.json`: statement, now split; retained the statement and the existing mapping-space argument, divided the long construction/pasting step, and cited existing general lift initiality after passage to the opposite for the final fiber comparison. Removed the unused `lem-coef-pointed-model-stability` statement dependency. Mathlib verdict: no match for quasicategories.
- `citations.json`: 21 verbatim excerpts, one for every step/node citation.
- `searches.jsonl`: actual search-command records; the node retains its older records and appends this session's records.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script, not part of the DAG delivery.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not its unit's key statement.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint identifier and arrow-target, codomain-fibration, Cartesian-arrow and quasicategory terminology. No project declaration stating all clauses was found. The item has no recorded Lean audit declaration. Nothing was compiled, and the upstream master sorry declarations were not treated as proofs.

## Wanted sources

WANTED: Jacob Lurie, Higher Topos Theory, Lemma 6.1.1.1, Proposition 2.4.4.3, Remark 2.4.1.9, and Section 1.2.1, archival copy for lem-coef-arrow-target-cartesian-pullbacks. The IAS URL timed out; I read the author's Harvard PDF, https://people.math.harvard.edu/~lurie/papers/HTT.pdf, online instead (printed pp. 531–532, 131 and 119 respectively).

WANTED: Cisinski, Higher Categories and Homotopical Algebra, Theorem 6.6.9 and Remark 6.6.11, archival copy for the existing mapping-space pullback criterion; read https://cisinski.app.uni-regensburg.de/CatLR.pdf online.

WANTED: archived Kerodon sources for Tags 01F1 (exponential isofibration), 06BZ (arrow mapping spaces), and 0110 (homotopy-pullback pasting); read the corresponding https://kerodon.net/tag/ pages online. These are Kerodon identifiers, not Stacks tags. No Stacks tag states the quasicategorical result, and none is invented here.

## Findings and corrections

The starting item already contained a substantial proof but had `status: unsplit`. There was no earlier sandbox node, report or search log to recover. I copied that item and preserved its statement, ancestry and historical search evidence. Its model-stability statement dependency was extraneous: the assertion quantifies over arbitrary quasicategories with cospan pullbacks and never mentions a pointed model category.

The construction/pasting argument formerly occupied one 2,430-character step. It is now Steps 2–3, with the same mapping-space formula and both directions of the cited pasting rule displayed explicitly. The original final mapping-fiber uniqueness calculation has been replaced by the existing general cocartesian initiality result on the opposite inner fibration. This avoids relying on an implicit compatibility of homotopies inside a homotopy fiber. No lemma was created to restate a clause of the item. The item still asserts only the equivalence of lift objects in the fiber, with no coherent choice of a transport functor added.

The inherited ancestry describes an older supporting presentability/GHN subargument. I read the current main-20261015 ancestor at `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md`, and the older master ancestor with its proof. The current file no longer contains the historical GHN proof paragraph. I preserved the maintainer-owned unit and historic ancestry; the immediate parent `lem-coef-relative-cone-presheaf-fibers` explicitly uses precisely this arrow-target pullback-square assertion. This delivery is a generic tool proof below that parent, not a replacement of the chapter or unit route. The existing off-unit functor-category tool declaration is retained in `split_report.tool_uses`.

## Unfinished work

None for this one-level split. Existing cited foundation nodes retain their own current states. Archival source requests above remain requests, so the mapping-space proof is honestly marked `proof_origin.by: agent`.

## Not duplicates

No new nodes. Whole-DAG searches for `6.1.1.1`, target evaluation and codomain fibration, and whole-blueprint searches using `tools/blueprint_refs.py` for target evaluation, Cartesian lifts and codomain were inspected. Broader arrow/Cartesian searches showed no other blueprint statement equivalent to the item; `blueprint.same_as` remains empty. The general cocartesian initiality and simplicial-opposite nodes were reused, as were all the existing mapping-space ingredients.

## Review by NZ

I read the item against HTT Lemma 6.1.1.1, including its proof on printed pp. 531–532 and the following transport discussion. Its hypotheses are an arbitrary quasicategory, with cospan pullbacks needed only for existence of Cartesian lifts. The lemma's edge characterization does not assume presentability or a terminal object. Remark 2.4.1.9 supplies uniqueness with fixed base edge and fixed target; it is an equivalence of lifts, so the item's fiber comparison is the correct objectwise conclusion. I read the chapter and unit records, the immediate parent's application, and both available ancestor texts. No source statement has been weakened or corrected and no coefficient categories have been identified.

For Step 1 I opened `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-isofibration-exponentiation`, and `def-coef-infinity-fibrations`. The first explicitly makes Fun(K,C) a quasicategory, and the second explicitly makes restriction along any degreewise injective A→B an isofibration. Here A={1} and B=Delta^1 are small. The definition then provides the inner-fibration condition. Describing the strict fiber's simplices and restricting an inner-horn lifting problem to a constant base simplex are direct applications of the displayed degreewise pullback definition, not an assertion that this fiber is a full subcategory.

For Step 2 I opened `def-cbc-enhanced-diagrams-cones`, `lem-coef-infinity-terminal-pullback-criterion`, `lem-coef-infinity-cartesian-mapping-criterion`, and `lem-coef-infinity-arrow-morphism-square`. The cospan hypothesis supplies the cone. The terminal-pullback statement explicitly concerns a coherent square presenting that cone. The arrow-morphism statement supplies both displayed homotopy fiber products, their endpoint projections and naturality in the second arrow. Thus the vertical maps really are target evaluation; this is not an ordinary Hom-set formula. The Cartesian criterion applies because Step 1 has already proved an inner fibration between quasicategories.

For Step 3 the terminal-pullback statement gives the represented pullback with test object w. The pasting statement explicitly gives both pasting and cancellation when the right square is a homotopy pullback, including specified commutation homotopies. I checked the corners: the first rectangle ends at Map_C(w,z) above Map_C(w,c), and the right square to be cancelled is exactly the endpoint square for v'. Naturality and endpoint compatibility from the arrow-morphism statement identify this with the Cartesian-criterion square. No change of coherence or unjustified replacement of a strict pullback by a homotopy pullback is used. All four statements are named in this step.

For Step 4 I reread the same Cartesian, arrow-morphism, pasting and terminal-pullback statements, and `lem-coef-infinity-mapping-composition`. The latter explicitly says that composition by a degenerate identity is homotopic to the identity. The test arrow is 1_w, so the extra path-pullback factor contracts: its projection has the constant-path section and a contraction obtained by moving the free path endpoint towards its fixed endpoint. With the chosen unit homotopy this gives the required equivalence. The endpoint-projection compatibility ensures that the resulting comparison is the comparison of the given square. It is checked for every w, as the terminal-pullback criterion requires. The forward calculation works for every pullback square, not just one chosen lift. Finally the definition of Cartesian fibration applies to the lift supplied for each given edge and target. No terminal object is used.

For Step 5 I opened `lem-coef-simplicial-opposite-homotopy-calculus`, `def-coef-infinity-fibrations` and `lem-coef-infinity-cocartesian-composition-initiality`. Opposite preserves quasicategories, inner fibrations and degreewise fibers and exchanges horn i with n-i. Thus Cartesian final-horn lifts become cocartesian initial-horn lifts with the same source and same base edge. The initiality node explicitly concludes equivalence of their targets in the base fiber after forgetting the comparison triangle; its statement, not a detail hidden in its proof, supplies exactly what is used here. Reversing an equivalence reverses the two inverse triangles, so the result lies in the original fiber as required. This general initiality statement is smaller than this item and already exists, so it was cited rather than recreated.

I tested the assertion on the empty quasicategory (the lifting assertions are vacuous), a discrete quasicategory with multiple objects (pullbacks exist but no terminal object is forced), an ordinary nerve with pullbacks (the criterion is the usual codomain-fibration square criterion), and an identity base edge (a pullback square gives a fiber equivalence). These cases check that no nonemptiness, pointedness or finite-limit hypothesis has slipped in. In particular the empty and disconnected cases rule out smuggling in a terminal object.

I checked delivery-errors B–E with the statements open. There are no new statement-only nodes or Mathlib leaves needing metadata checks. All non-elementary ingredients in the five steps have citations; all 21 excerpts in citations.json are literal substrings of the corresponding node statements. All steps are honestly non-elementary. The former long step is now two explicit calculations, and no step exceeds 2,000 characters. Mathlib searches were run through msearch.py in four kinds, with a second semantic phrasing; the returned `IsCartesian`, `pullbackMap` and `Arrow.hasLimitsOfShape` facts concern ordinary categories, as confirmed in Cartesian.lean and Fibered.lean. They do not give the quasicategory theorem, nor does a Quillen Kan-fibration instance. No false no-match claim was recorded for an unavailable service.

The server `review_split` check passed with zero new nodes. The complete required dry run and direct delivery follow this report.
