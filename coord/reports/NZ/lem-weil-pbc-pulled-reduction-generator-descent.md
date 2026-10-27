# Stage-1 report: lem-weil-pbc-pulled-reduction-generator-descent

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-pulled-reduction-generator-descent.json`: statement, now split in seven steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation per cited node per step.
- `searches.jsonl`: actual search-command log for this item; no invented queries.
- `report.md`: this report.

0 new nodes; 0 new Mathlib leaves. No Lean written or compiled. No repository or launcher files edited. Sandbox was empty of prior work on resumption; no interrupted delivery was active.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by pulled-reduction and normalization/cocycle concepts. Existing unrelated cocycle and etale resolution declarations do not state this item. The source library contains no declaration found that supplies all these clauses.

## WANTED

None. The relevant blueprint and Stacks sources are present.

## Corrections and scope

Statement unchanged, including the explicit distinction between constant and completed coefficient sheaves. The imported item was statement-only. Existing flat-model formulas already supply the maps and inverse maps, the model classes, and the identifications with the specified derived comparisons. Recreating those as new nodes would duplicate the existing lemma. The square, triple and unit computations are short consequences of these formulas and the ring-map laws, so they remain elementary proof steps. The descent argument uses an existing localization leaf instead of making another general descent lemma.

The blueprint route remains main-20261015 `lemma-weil-pbc-completed-pullback-reduction`, its compatibility with normalization cocycles and its finite pullback/tensor comparison. This is auxiliary coefficient calculus below that node, not a replacement for any unit or chapter argument. Blueprint searches for K-flat and normalization cocycles returned no exact alternative statement. The ancestor command confirms `lemma-weil-pbc-completed-pullback-reduction`.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-pulled-reduction-flat-model-formulas`, `lem-weil-pbc-localization-universal-property`, and `lem-weil-pbc-site-derived-tensor-descent` after reading their statements. The generic tensor-comparison-descent-representatives node was inspected but not used: its bifunctor hypotheses add unnecessary apparatus here.

## Review by NZ

I read the main-20261015 completed-pullback-reduction statement and proof, especially the compatibility assertion in the first paragraph and the finite pullback/tensor formula in the second. The blueprint does not give the tensor calculations; those calculations are my argument, so proof_origin is agent. For the derived part I read Stacks sites-cohomology.tex, lemma-factor-through-K-flat (Tag 0G7D), lemma-pullback-K-flat (Tag 0G7E), and lemma-derived-base-change (Tag 06YY). I also read the categories.tex localization property at Tag 04VG and Mathlib Localization/Predicate.lean's liftNatTrans, liftNatTrans_app, comp_liftNatTrans, liftNatTrans_id and liftNatIso. The natural-transformation part is explicitly supplied by the existing Mathlib localization node, rather than attributed to a stronger Stacks sentence. There are no new-node sources to review.

For step 1 I opened the entire flat-model-formulas statement. It really gives actual balanced sheaf-complex isomorphisms, inverses, and the flat-term K-flat intermediate outputs, including successive quotient tensors. The section-calculus definition explicitly says that pure sections determine maps out of the actual sheaf tensor. Applying that statement repeatedly to iterated tensors justifies testing the equations on pure sections without claiming that all sections globally are pure.

For step 2 the cited model formulas give precisely the images for t, h, and n. The adic-datum statement defines q by postcomposition with quotient ring maps and states their compatibility. Thus q preserves products and carries the image of r at b to its image at a. I computed both outputs in the same S_a-module; no coefficient ring was identified with a different ambient ring.

For step 3 the model statement supplies the h and n formulas and the before-inverse-image normalization. The datum gives q_ba q_cb = q_ca. The successive-derived-quotient-normalization statement specifies the scalar associator (x tensor s) tensor t maps to x tensor b(s)t, including its iterated compatibility. These statements give precisely the reassociation used in the displayed triple calculation. The same section-calculus determination extends the resulting equality to sheaf morphisms. No pullback-composition coherence theorem is silently used.

For step 4 q_aa is the identity by the datum. Inserting it into the model formulas gives scalar multiplication; I wrote the balancing equation that checks its inverse. The section-calculus citation supplies the passage from sections to morphisms, rather than relying on a claim only before sheafification.

For step 5 the formulas are natural because both orders substitute f(x), and I wrote the differential formula with coefficients in degree zero from def-pc-tensor-complex-sheaves. This removes possible tensor signs. Termwise additive functors preserve the equation f-fprime = dH+Hd simply by applying them to that equation; this is an elementary check that the transformations pass to homotopy classes, not a claim that arbitrary maps of resolutions can be chosen canonically.

For step 6 I read the full statements of lem-pur-derived-change-of-rings and lem-weil-pbc-ringed-topoi-derived-pullback. The former states preservation of quasi-isomorphisms between K-flat inputs and canonical comparisons compatible for a third resolution. The latter separately states preservation for flat-term K-flat inputs and the corresponding natural composable computation maps. Every intermediate class required is explicitly provided by the model-formulas node. Restriction preserves quasi-isomorphisms because it leaves underlying abelian sheaves and their cohomology unchanged; the restriction definition supplies that same-underlying-sheaf description. The proof does not infer arbitrary-flatness from a definition or assert exactness of quotient extension.

For step 7 the site-derived-tensor-descent node states exactly the equivalence W^{-1} P = D for the full homotopy subcategory with flat K-flat terms. I use its equivalence assertion, not its later two-variable assertion for a one-variable transformation. The localization-universal-property statement supplies existence and uniqueness of lifted transformations, preservation of identities and composition, lifting of inverses, and detection of equality on models. These clauses justify every descent claim made. The flat-model statement identifies the very specified tau, thetaH and thetaN, so the final equality does not merely concern some isomorphic replacements. No completeness condition enters the availability of representatives.

I tested equal indices a=b=c (the scalar unit), the zero complex and zero module, the identity g, a constant tower, and nonflat quotient maps such as Z/4 to Z/2. The section calculations remain valid; the nonflat example explains why only K-flat quasi-isomorphism preservation is used. Both tensor factors outside P are in degree zero, and all sites are the stipulated small sites, so there is no extra size or boundedness assumption. Every step is shorter than 2000 characters and hides no separate comparison lemma: the substantive comparisons are cited existing nodes.

Mathlib searches used leanfinder, loogle, grep and two leansearch phrasings via the required command. I read the sheaf pullback associator in PullbackContinuous.lean (pullbackComp and pullback_assoc), the ordinary ring extendScalars_assoc in ChangeOfRings.lean, and the localization lifting declarations. The first two are underived generic associators and do not state the specific adic generator comparison and descent. The generic localization result is already a leaf in the DAG and is cited, not recreated.

## Unfinished work

None in this one-level split. The new split relies on the existing statement-only flat-model-formulas lemma as an ordinary DAG dependency; proving or splitting that separate node is not part of this item.
