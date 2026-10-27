# Worker report: lem-sfb-curve-smooth-polarization-cover

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-curve-smooth-polarization-cover.json`: statement, split in four steps; statement and statement dependencies unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-picard-stack-smooth.json`: one new statement-only node, unsplit, no Mathlib match. It states algebraicity of the Picard stack for an algebraic-space total space, and smoothness when geometric fibres have dimension at most one. It does not assert the existence of any ample line module or any schematic base change of the family.
- `citations.json`: a verbatim statement quotation for every cited node in each numbered step.

No Lean was written or compiled. No repository or launcher file was changed. Temporary assembly code and search logs are confined to this item's sandbox. The source node had no split or report in the sandbox when this attempt began; the earlier search log was retained and read.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and polarization-cover terminology found no declaration stating this item. The Picard chapter concerns schemes, principally smooth projective curves; it does not prove this assertion for arbitrary proper flat finitely presented algebraic spaces over arbitrary schemes. The Mathlib searches returned scheme smoothness/flatness lemmas and Picard groups of rings, not a Picard stack or relative polarization cover. I read the returned search types, the Smooth.lean definitions and composition result, and the ring `relPic` definition. Those results do not specialize to either the item or the new statement in one line. The actual query texts and outcomes, including the previous attempt's searches, are retained in searches.jsonl and copied faithfully into mathlib_searches; no unavailable search is represented as a negative result.

## WANTED

None. The mathematical sources used are present under literature/stacks-project/; the current blueprint was read under literature/blueprint/latest/.

## What needed correction

There is no statement correction. The item correctly includes empty, nonreduced, disconnected and zero-dimensional fibres and does not assume a Noetherian base. Its imported proof was empty. A tempting use of `lem-sfb-picard-stack-curve-geometry` would be invalid: its morphism and line-module definitions concern schemes, whereas here the total space is an algebraic space until the ample locus is imposed. I added the algebraic-space Picard-stack input rather than silently assuming the desired schematicity. Likewise I did not use `lem-sfb-picard-space-curves-smooth` or `lem-sfb-flat-proper-picard-algebraic-space`: they impose universal O-pushforward hypotheses and concern the Picard sheaf, rather than the line-bundle stack.

The nearest-blueprint-ancestor tool reports `None` for this already-created chain. I preserved the item's existing null from.node and the supplied ancestry and precise supporting place, and used that reported ancestor for the new node. The current unit and latest direct-images proof were read: this is a lower-level moduli prerequisite and changes neither the unit statement nor its route. No unit-realization record is due for this supporting node.

## Not duplicates

lem-sfb-space-picard-stack-smooth vs lem-sfb-picard-stack-curve-geometry: both cite 0D04/0DPJ, but the existing result is for a scheme total space (its flat/proper, base-change and module-pullback definitions and its split all use schemes); the new result allows an algebraic-space total space with small-etale line modules and their ringed-topos pullbacks. Applying the existing scheme result before proving schematicity here would be circular. The new result supplies a smooth Picard atlas, not an ample bundle on the family.

Blueprint searches for Picard stack, invertible sheaves, 0DPJ, 0D04, polarization and projective curves were inspected. None states the algebraic-space Picard-stack result. Whole-DAG searches by tags and concepts found the above narrower scheme result and the two Picard-sheaf results, not a generalization applicable here. The existing ample-locus, separated dimension-one schematicity and proper-curve projectivity results are reused, rather than duplicated.

## Review by Q96

I read moduli-curves.tex section-stack-curves, section-polarized-curves, the full statement and both proof paragraphs of 0DQ0 (lemma-polarized-curves-over-curves), and the first paragraph of 0E6F (lemma-etale-locally-scheme). The source specifies precisely proper flat finitely presented algebraic-space families of relative dimension at most one. Polarized objects have scheme total space and relatively ample ordinary line bundles. I realized its open-Picard-stack proof directly on a smooth scheme atlas, so a separate theorem on the stack of polarized curves is unnecessary.

For the sole new node, I read quot.tex 0D04 (proposition-pic) and moduli.tex section-picard-stack, 0DMB (lemma-pic-qs-lfp) and the full statement and proof of 0DPJ (lemma-pic-curves-smooth). The standing hypotheses explicitly allow algebraic spaces, impose flatness, properness and finite presentation, and do not assume that O pushes forward universally to O. These sources provide the new node's algebraicity and smoothness; the atlas and field-extension lifting wording unwinds the existing definition of algebraic stack and surjectivity. The node contains no proof, no hidden assertion of ampleness, and no chosen polarization. In a subsequent split its arbitrary-base infinitesimal lifting argument will need the appropriate algebraic-space cohomology and first-order Picard obstruction inputs; none is being claimed proved by this delivery.

Step 1 uses the new Picard-stack theorem exactly with f and its geometric-fibre bound. Its statement actually supplies a smooth surjective scheme atlas with smooth structural composite. An atlas map is an object of its explicitly defined line-module groupoid, so it gives M on X_V by definition. I explicitly keep X_V an algebraic space here; no scheme hypothesis is slipped in.

Step 2 uses `lem-sfb-space-flat-proper-fp-locality` for properness after arbitrary base change, and `lem-sfb-space-relative-ample-locus` for the universal open subscheme of V. I opened both statements. The latter explicitly gives schematicity, identifies the restricted line with an ordinary invertible module, and asserts ampleness over every affine open, without Noetherian assumptions. I also read its source spaces-descent.tex 0D3D (lemma-ample-in-neighbourhood). The morphism q is smooth by step 1, so `lem-pc-open-immersion-smooth-composition` applies to its restriction to U. This is a generic scheme tool, not a replacement moduli route.

Step 3 uses base-change properness, then the existing `lem-sfb-separated-space-dimension-one-scheme`, whose hypotheses are only a separated locally finite-type space over a field with dimension at most one. Properness supplies the separation and finite-type hypotheses. I read spaces-over-fields.tex 0ADD (lemma-codim-1-point-in-schematic-locus) and the existing node's full statement. Once C is a scheme, `lem-sc-proper-dim-one-projective` applies without smoothness or reducedness: I read its statement and varieties.tex 0A26 (lemma-dim-1-proper-projective). It gives an actual closed immersion, not merely an abstract existence of an ample object. `lem-pc-very-ample-ample` explicitly produces the ample O(1) pullback and its field-extension ampleness. Its latest blueprint statement/proof were read. Finally `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` explicitly identifies ordinary invertible modules with small-etale line modules; this supplies an actual object of the Picard stack, not a Picard-sheaf class.

Step 4 invokes the new node's explicit field-extension lifting clause, giving v and an isomorphism of M_v with A_K. The field extension need not itself be algebraically closed: the existing O(1)-ampleness node covers every field extension. The full scheme/etale equivalence statement includes compatibility with pullback for every scheme morphism, which is exactly the compatibility used here. The universal test property of the ample-locus node, not merely openness on points, then factors Spec K through U. Passing from this lift to a point of U over t is elementary. This proves surjectivity even when the base is not quasi-compact. No algebraic-space dimension comparison, descent of ampleness or unmentioned Picard-representability theorem is hidden in this step.

I checked B--E against the written nodes: every object of the new statement is introduced, small-etale line modules and module pullback are specified, the new node is statement-only with all definition dependencies, and every non-elementary proof input is a cited statement, not a claim extracted from another node's proof. The citations file contains literal copies of those statements. Existing dependency paths were inspected to ensure that none of the reused inputs depends on this item. The only new node is strictly different from the item's conclusion: Picard-stack smoothness has no ampleness or schematicity conclusion. No step exceeds 2000 characters. No prohibited SGA source is used.

Edge cases: for an empty geometric fibre the Picard groupoid has its unique line module up to unique isomorphism and the empty scheme is projective with ample O(1) pullback; the cited projectivity statement explicitly allows the empty scheme. Finite nonreduced fibres and reducible or disconnected one-dimensional fibres satisfy the cited dimension-one theorems; no genus, purity or connectedness is used. If T is empty the construction restricts to the empty base and surjectivity is vacuous. These checks did not require any statement change.

## Unfinished work

The one new Picard-stack node remains unsplit, as required for a one-level stage-1 delivery. All proof steps of the assigned item are supplied. Server dry-run and delivery results follow from the required delivery tool.
