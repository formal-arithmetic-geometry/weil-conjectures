# Q110 stage-1 report: lem-trf-site-pullback-injective-evaluation-acyclic

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-site-pullback-injective-evaluation-acyclic.json`: statement, now split in four steps; not a Mathlib leaf. Statement and statement dependencies unchanged. No new nodes or Mathlib leaves.
- `citations.json`: one verbatim-statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch log. `prepare_split.py` is the sandbox-only preparation script.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` source for the exact item id/blueprint tag and for pullback, injective, evaluation, acyclicity, cocontinuity, and the source label. No declaration states this general-site result. The pro-etale comparison acyclicity declaration in `SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean` assumes scheme-theoretic quasi-compactness/quasi-separatedness and concerns a different direct-image functor, so is not an attachment. Upstream master was read as reference only.

## WANTED

None: all sources used are present in `literature/stacks-project/`.

## Corrections and source audit

The item was statement-only and had no split or report in this sandbox; its repository version has no own Lean audit declaration. Its statement is faithful to Stacks Tag 0D6X, `sites-cohomology.tex`, `lemma-pullback-injective-pre-limp`, with the integer-module specialization interpreted directly in abelian sheaves. No statement dispute or added hypothesis was needed. All existing metadata and prior search records were retained.

The proof does not assume that inverse image preserves injective objects. The nearby Tag 0D6Y (`lemma-pullback-injective-limp`) has an extra fibre-product condition for total acyclicity; that stronger result is unnecessary here. The general-site vanishing criterion is already `lem-weil-pbc-site-cech-vanishing-criterion`; the similarly named node without `site` only treats a scheme's small etale site. The source's injective-module Cech lemma can be replaced by its abelian-sheaf instance, the existing 03AW node, since the item already assumes an injective abelian sheaf. Thus no extra module/abelian cohomology comparison is hidden in the proof.

The ringed-site direct-image lemma `lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic` was also read but not cited: it requires a morphism of sites in the opposite direction presented by u. Its hypotheses cannot silently be inferred from this continuous-cocontinuous u. The elementary nerve comparison instead follows precisely from continuity as defined in 00WV.

## Not duplicates

No new nodes. Searches of the entire DAG by 0D6X, `pre-limp`, pullback/injective/acyclicity and Cech-vanishing terminology found the existing ingredients, which are reused. Whole-blueprint searches by 0D6X, `pre-limp`, `continuous and cocontinuous`, `cocontinuous`, and `injective` found no imported statement equivalent to the item; the pro-etale injective-comparison blueprint nodes have different sites and hypotheses. The item's `blueprint.same_as` remains empty.

## Route and tool uses

Read the trace-formula chapter record, the `sk-i-curve-zero` unit record and its steps, the current `blueprint_update` of the nearest blueprint ancestor `lem-trf-local-term-locality`, and the parent `lem-trf-site-object-derived-sections-pullback`. The inherited ancestry is the normal-cone/Orgogozo/ph-etale comparison chain; this item provides exactly the 0D6X input to its bounded-below 0DD8 comparison. It neither realizes the whole unit nor edits its realized fields.

The continuous-cocontinuous adjunction, injective Cech vanishing, and general-site Cech vanishing criterion are declared as generic tool uses in `split_report.tool_uses`. They are the black boxes that the source proof expressly calls for. No chapter/unit route is replaced, no unit metadata is changed, and no SGA source is cited.

## Mathlib searches

Ran msearch for the item with LeanFinder, Loogle, grep and LeanSearch, then a second semantic phrasing and a second grep. The exact queries and returned summaries are copied from `searches.jsonl` into the node; no unavailable service was reported as absence. Read the returned local-injectivity source (`PreservesLocallyBijective.lean:35`), continuous-cocontinuous adjunction (`CoverLifting.lean:322`), and generic injective derived vanishing (`Abelian/RightDerived.lean:153`). The first concerns injectivity of morphisms locally; the second supplies an adjunction only; the third requires the input object itself to be injective. None specializes in one line to evaluation-acyclicity of this inverse image. No new-node searches were required because no new node is created.

## Review by Q110

I read the complete statement and proof of Stacks 0D6X in `sites-cohomology.tex`. I also read its general-site Cech criterion 03F9 and its proof, the abelian-injective Cech vanishing 03AW and its proof, and Sites 00WV/00XR. The common-universe convention and all five statement-definition nodes were checked; the item concerns ordinary derived evaluation in abelian sheaves, not a newly defined cohomology theory. There are no new nodes whose statements or sources require separate review.

Step 1 uses the statement of `lem-weil-pbc-continuous-cocontinuous-topos-adjunction`, which explicitly defines L by L(G)(V)=G(u(V)), identifies it as g inverse image, specifies restriction maps, and preserves finite limits. Its assumptions are exactly the two properties of u in the item. Applying its formula to the group operations gives the abelian formula, with no claim about preserving injectives.

Step 2 uses `def-weil-pbc-sites-and-cohomology` clause (3), which explicitly includes both preservation of coverings and preservation of pullbacks of a covering member. It uses `def-weil-pbc-site-cech-complex` for the chosen iterated products and omitting-factor projections. I checked the induction: append a member of the original cover to the previous product over U, so every application is an instance of (3)(b), rather than arbitrary finite-limit preservation by u. The face-map identity follows by checking projections and their universal property; this is the elementary argument retained as a step.

Step 3 uses the actual product-group and alternating-differential formula of `def-weil-pbc-site-cech-complex`. I checked variance: c maps u(W) to the product P, so I(c inverse) maps I(u(W)) to I(P). The face-map identity from step 2 makes every restriction square commute, hence also the signed differential. An invertible chain map gives inverse maps on kernels modulo images. The cited statement of `lem-weil-pbc-site-injective-cech-acyclic` says positive Cech cohomology of an injective abelian sheaf is zero for every covering. Its target-site, coefficient and covering-index universe requirements hold under the common-universe hypothesis. The injective object is I on D, never F on C.

Step 4 uses the statement, not the proof, of `lem-weil-pbc-site-cech-vanishing-criterion`. I checked all three hypotheses: all objects and intersections are in B because B is all objects; the chosen collection is the actual set of all site coverings and is cofinal by identity refinement; step 3 gives positive Cech vanishing for every such covering. Its conclusion is explicitly the ordinary cohomology over an object defined by right-derived evaluation, which is exactly the item's conclusion. In particular the specialized etale-site criterion would not have sufficed, and was not cited.

I tested u the identity (injective evaluation vanishing), I=0, a site with no objects, singleton identity covers, repeated cover members, and a permitted empty covering. In the empty-cover case the positive Cech terms are empty products, hence zero abelian groups, and the argument still applies; no nonempty-index hypothesis was used. The product choices are compared by their canonical isomorphisms, and no subcanonical-site or terminal-object assumption occurs. Positive integers p are precisely positive natural cohomological degrees. Every step is below 2000 characters; the nerve/complex comparison is written explicitly and contains no separate non-elementary claim. Each cited statement was opened, and each entry of citations.json was checked as a literal substring of that statement. There are no new-node duplicates, relabelled clauses, statement-only node proofs, or new cycles introduced by a dependency on the parent.

## Unfinished work

None in the mathematical split. The required server dry run exited successfully: `OK (not pushed) deliver/Q110/lem-trf-site-pullback-injective-evaluation-acyclic at 168feadce2: preflight passed`. It ran the maintainer preflight, including the DAG and split checks. The final push invocation performs the same delivery validation.
