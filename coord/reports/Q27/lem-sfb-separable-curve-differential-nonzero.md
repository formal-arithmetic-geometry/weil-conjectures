# Stage-1 report: lem-sfb-separable-curve-differential-nonzero

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-separable-curve-differential-nonzero.json`: statement, now split in six steps; no exact Mathlib match. The statement and its statement dependencies are unchanged. Its inherited searches were preserved and five actual Q27 searches added.
- `citations.json`: thirteen entries, covering every step/node pair; quotations copied verbatim from the cited statements, including their hypotheses.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is a sandbox-only preparation script, not a project or delivery tool.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: differential localization, associated-sheaf stalk localization, integral affine fraction fields, and differential scalar extension for finite separable fields. No existing node other than the assigned item was edited.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, separable differentials, generically etale maps, cotangentMap and nonzero differentials gave no declaration stating the whole item. The differentials module constructs differential sheaves and their rank theorem; it does not already prove the assigned map nonvanishing. The other existing criterion `lem-a1-nonzero-differential-generically-etale` only equates nonvanishing with an etale open and supplies no finite-separability implication. No sorry declaration was counted as a proof.

## Literature wanted

None.

## What was wrong or incomplete

The item had its correct statement but an empty proof. Stacks 0C1C leaves some generic-point details omitted. The split now writes the map identification and the nonzero-target check, rather than quoting 0C1C as a black box or moving the whole assertion into another node. No hypothesis, conclusion or definition was changed.

The inherited `created.item` ancestry terminates at the module name `Sheaf.SixFunctors.CtfStabilityDirectImages`, so `tools/blueprint_refs.py ancestor` prints None. I retained the inherited null `blueprint.from.node` and its via list, and made the place explicit. The intended blueprint ancestor is identifiable from the recorded route as `det-thm-sf-ctf-stability-direct-images`; its current main-20261015 proof (3) uses proper/open direct image and compactification. The extended alteration/high-genus/Riemann--Hurwitz route is in the existing DAG, not a sentence explicitly present in that blueprint paragraph. This delivery continues that existing route and changes neither chapter nor unit.

## What could not be finished

Nothing in the one-level split. The proof depends only on existing nodes. This is stage 1; no Lean file was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs. Whole-DAG searches by differential/generic/separable concepts and source tags found the general tools used in the proof. Whole-blueprint searches `differential`, `separable`, `0C1C`, and `generically.*etale` found no blueprint declaration identical to the item. In particular, the existing nonzero-differential/etale-open criterion does not include condition (5).

## Review by Q27

I read the complete B--E delivery error checklist and compared the six proof steps with the node statements and sources. For the item I read Stacks `curves.tex`, Tag 0C1C (`lemma-generically-etale`), including its five conditions and proof; its first paragraph supplies the rank-one/generic-point viewpoint. I also read the relevant chapter and unit records and the current blueprint's direct-images proof (3). There is no new node requiring a separate source review.

Step 1 uses `def-sc-function-field` for the unique generic point and its function-field stalk, and `lem-sc-integral-function-field-affine-fraction` for the affine domain/fraction-field identification. The latter states exactly that any nonempty affine contains the generic point and that its germ map gives the fraction field. Dominance sends generic point to generic point by the explicit closure argument written in the step; no unproved generic-fibre theorem is used. Both schemes are integral by the curve hypothesis, so the general integral-scheme clauses of the cited statements apply, without invoking their older nonintegral-curve convention.

Step 2 cites `def-pc-curve` and `def-sbc-smooth-morphisms` to verify smooth relative dimension one: there is a single fibre, the integral dimension-one scheme X, so it is equidimensional of dimension one. The latter node explicitly includes this fibre characterization of relative dimension. `lem-sc-smooth-omega-finite-locally-free` then applies with d=1 over Spec k; its statement is over arbitrary schemes and its recorded closed Lean declaration also has no algebraically-closed-field restriction. I read Stacks `morphisms.tex` Tag 02G1 (`lemma-smooth-omega-finite-locally-free`) and the following definition. `def-amb-finite-locally-free-module` states the local trivializations used to take a rank-one stalk. The field L is nonzero, so the basis germ is nonzero. I did not use the older canonical-sheaf node, whose definition dependencies have a narrower curve convention.

Step 3 cites `def-sc-relative-differential-sheaf` for its affine associated-module description, `lem-weil-pbc-spec-tilde-stalk-localization` for the germ/localization comparison, and `lem-weil-pbc-kahler-differentials-localization` for its derivation-compatible isomorphism. I read Stacks `morphisms.tex` Tag 01UT (`lemma-differentials-affine`), `schemes.tex` Tag 01HV (`lemma-spec-sheaves`, clauses (6)--(7)), and `algebra.tex` Tag 00RT (`lemma-differentials-localize`, clause (2)). In a domain the generic prime is (0), and the multiplicative set is exactly the nonzero elements. Thus every localization hypothesis is satisfied and no base-ring localization comparison is silently assumed.

Step 4 uses `lem-weil-pbc-module-stalk-pullback` for both its displayed tensor formula and its final clause on germs of pulled-back sections. I read Stacks `sheaves.tex` Tag 0098 (`lemma-stalk-pullback-modules`). The point is eta_X, its image is eta_Y from step 1, and the local ring map is precisely K to L. `def-a1-relative-differentials-pullback-map` gives the formula on local functions, and `def-weil-pbc-kahler-differentials` gives generation by the symbols db. I read `morphisms.tex` Tag 01UV (`lemma-functoriality-differentials`) for that formula. Representing b in the stalk by a local regular function proves the entire compatibility on tensor generators; this is an explicit computation, not an uncited identification theorem. Switching the tensor factors is the ordinary commutative-ring tensor flip. No gluing, flatness or derived comparison is hidden here.

Step 5 uses exactly `lem-weil-pbc-separable-algebraic-differentials-base-change`: the tower consists of fields and L/K is finite separable as the hypothesis requires. Its stated generator formula is identical to the map in step 4. I read its whole statement and Mathlib match record, Stacks `algebra.tex` Tag 090W (`lemma-characterize-separable-algebraic-field-extensions`) and the differential computation in the proof of 031W (`lemma-derivative-zero-pth-power`). Perfectness of k in 031W is not imposed on this item: the cited existing general scalar-extension node states the arbitrary-base-field result, with the formally etale Mathlib equivalence as its match. The nonzero target was proved in steps 2--3. Step 6 is elementary: the zero sheaf map has zero germ maps by the definition of a germ map.

For C1/C4 I opened every cited node and copied its whole statement into `citations.json`, so the hypotheses as well as the precise formula can be checked. No step uses a cited node's internal proof. Every non-elementary fact is covered by a named node; the conclusions follow by applying the displayed statements and the written generator argument. The only off-unit generic tool that might need a route declaration is `lem-weil-pbc-module-stalk-pullback`; I declared it in `split_report.tool_uses` as allowed by the standing brief, without setting the maintainer-owned top-level `tool_uses` field. Other non-definition tools are Mathlib leaves or the already closed rank theorem.

For B/D I created no statement-only proxy for a clause, no elementary node and no duplicate. The original statement remains self-contained, including dominance, smoothness, integrality, dimension one and finite separability. The item is not declared a Mathlib leaf: searches returned algebraic differential results, polynomial derivatives, general smooth/unramified properties and manifold notions, not the geometric assertion in one specialization. I read all returned hits and used two distinct semantic phrasings; the exact actual search records, including zero-hit results, are retained. There was no unavailable service. Tags 0C1C, 02G1, 01HV, 00RT, 0098, 090W and 01UV were checked in the Stacks tag table.

For E I checked the identity map and open immersions (generic differential is an isomorphism), a separable ramified map t maps to t^n with n prime to the characteristic (its derivative may vanish at a closed point but is nonzero generically), and Frobenius in characteristic p (differential zero, excluded because the induced extension is inseparable). No finite morphism, properness, perfectness of k or rational closed point is used. Dimension zero would allow a zero differential target and is excluded by the curve hypothesis. The statement is true as written; no STATEMENT-DISPUTED correction is needed. All non-elementary steps are under 1000 characters, and none hides an independently hypothesized comparison or standard lemma: the comparisons are direct applications of existing general nodes followed by the explicit formula.

## Validation

The required `deliver.py Q27 lem-sfb-separable-curve-differential-nonzero --no-push` exited successfully and printed `OK (not pushed)` at dry-run commit `c24724ed051`: server preflight passed, including the required DAG and split checks. The final push is performed by the same authorized delivery tool, which checks the final report as part of its delivery. No local checker or compiler was run.
