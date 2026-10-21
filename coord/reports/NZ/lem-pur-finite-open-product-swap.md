# Stage-1 delivery: lem-pur-finite-open-product-swap

Group NZ, 2026-10-21. Direct delivery with the worker's signed review below.

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-open-product-swap.json`: statement, split into nine proof steps. The statement and its hypotheses are unchanged. No Mathlib match for the whole comparison.
- `citations.json`: 23 step/node pairs, each with a verbatim substring of the cited statement.
- `report.md`: this report. `searches.jsonl` was written by the prescribed msearch command; the original item searches are retained, and the five actual NZ searches have been appended to the item's search records.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the literal item tag, finite/open/product keywords, and open tensor, extension-by-zero and external tensor notions. In particular I read the scope of `SixFunctors/ProEtale/ModuleObject/Derived/OpenLowerShriekInterchange.lean` and `OpenLowerShriekBaseChange.lean`: these concern condensed/module-object bounded-constructible operations or proper/open interchange, not every clause of this ordinary constant-module unbounded signed product comparison. No exact attachment was found. No Lean was written or compiled.

## WANTED

None. All sources used are available in the read clone.

## What needed repair or clarification

The imported item had no proof. Its Stacks citation was already explicitly described as background for an agent-formulated comparison, rather than a claim that 0GL1 itself states signed product coherence. I retain that distinction and mark the proof agent-written. The background is Stacks `sites-cohomology.tex`, Tag 0GL1, `lemma-j-shriek-and-tensor`, whose actual assertion is the unbounded derived open tensor identity. I read its statement and K-flat proof. The local blueprint context read was `main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md` (symmetry paragraph) and `sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md` (Steps 3--4). The latter's even-shift assertion alone does not prove interchange of the actual product maps: this item supplies the earlier open-product comparison, with signs in arbitrary degrees. The unit `sk-prop-an` Step 6 and the chapter record were read; no chapter/unit route is replaced.

A second subtlety is that the existing split proof of `lem-cbc-extension-zero-composition` discusses etale restriction models. I do not take an unbounded pro-etale unit equation from that proof. Step 2 derives it anew from the statement of the generic composite-adjunction definition and the generic conjugate-isomorphism unit-equation node, applied to the pro-etale derived adjunctions explicitly supplied by `lem-sf-open-tensor-normalization`. The canonical compositor is the mate of restriction composition; its restriction identity is the displayed unit equation. Thus the existing canonical compositor named in the item has its correct normalization, rather than an arbitrary scalar multiple of an isomorphism.

No statement dispute or missing hypothesis was found. The harmless repeated letter k in the supplied mathematical text denotes the field and, in the open-immersion notation, the second immersion; in the proof these roles are distinguished by their typed domains.

## Unfinished work

None for this one-level split. Existing dependencies retain their own stage states. No subsidiary result is newly declared or split.

## Searches and reuse

The item itself was searched using the prescribed commands, with the exact queries recorded by the tool and copied into `mathlib_searches`. LeanFinder was tried in two phrasings, LeanSearch and Loogle returned hits, and the prescribed Mathlib grep returned no extension-by-zero hits. I read Mathlib `CategoryTheory/Monoidal/ExternalProduct/Basic.lean`, especially `externalProductSwap`: its arguments are functors on product indexing categories, and it does not construct the scheme open-extension product comparison. The other hits concern light condensed monoidal categories, ordinary graded tensor products, structure-sheaf restriction, or geometric stability of open immersions. They do not specialize in one line to the whole item. No unavailable service was described as absence.

Before considering subsidiary nodes I searched the whole DAG for the source tag 0GL1 and the open/tensor/product notions, and used `tools/blueprint_refs.py search` for `product swap`, `open tensor`, and `0GL1`. The ancestor command confirms `prop-pur-affine-space-composition-law`. The existing generic nodes suffice; no new node is needed. The four projection identities for each intermediate product are written out rather than hidden in a new geometry lemma. The right-extension variant of the tensor comparison is a three-arrow composite and its two signs cancel in two lines; it is a proof step, not a new node.

## Not duplicates

There are no new nodes, so there are no new/existing same-tag pairs. For the item itself the nearest comparison is `lem-sf-open-external-tensor-normalization`: that node assumes a six-functor datum and bounded finite-Tor inputs, and also states a third-factor associativity assertion. This item has arbitrary unbounded constant-A modules and neither the six-functor datum nor the Tor hypotheses, so that node is not a usable theorem for this item's inputs. I read its statement and existing proof as useful prior work, then checked the required weaker-hypothesis argument against the statements of the lower nodes it uses. Neither `lem-sf-comparison-open-tensor-coherence` (etale/pro-etale comparison for etale-origin inputs) nor `lem-sf-integral-open-product-diagram-normalization` (actual integral reduction diagrams) has the same statement. None is cited to bypass its extra hypotheses.

## Review by NZ

I read the stage-1 brief, stage contract, SETUP's three blueprint levels, GOAL, and both copies of delivery-errors B--E. I checked the actual sources listed above with the item and each cited statement open. There are no new nodes requiring independent source validation. Every node used by every proof step has a corresponding exact quote in `citations.json`; I copied the complete normalization clause, including units, full faithfulness, beta/gamma isomorphisms and their restriction identities, so a generic definition is not being cited for any of those theorems.

Step 1 uses `def-pc-fibre-product` for its universal property and projection identities, and `lem-weil-pbc-open-immersion-base-change` for stability of open immersions. I read Stacks `schemes.tex` Tag 01JY, `lemma-base-change-immersion`, to check that it allows arbitrary base change. The composite-open assertion is only the elementary argument with open subsets and restricted structure sheaves from `def-weil-open-immersion`. Both middle schemes and the two different Cartesian squares for each factorization are displayed. No affineness, properness, or extra finiteness is used.

Step 2 uses the actual derived open adjunctions and units from `lem-sf-open-tensor-normalization`; `def-weil-pbc-composite-adjunction` explicitly gives its pasted unit, while `lem-weil-pbc-conjugate-iso-unit-equation` explicitly gives the unique isomorphism carrying that unit to the composite-open unit. `lem-cbc-extension-zero-composition` supplies the named canonical compositor. I checked Stacks `categories.tex`, Tags 0DV0 and 0B65, for the composite and mate calculus. The equality written in this step is what makes the restriction calculation about the specified map, not merely about two isomorphic objects.

Step 3 uses the gamma isomorphism from the normalization node and writes both signed symmetries before and after it. The signed formula occurs explicitly in `lem-pur-cochain-pullback-tensor-coherence`; `lem-weil-pbc-site-derived-tensor-descent` provides K-flat models and descent in unbounded derived categories. The signed-commutativity and composition clauses of `lem-pur-derived-pullback-tensor-iso` ensure these computations survive the specified restriction/tensor identifications. Applying symmetry twice gives the scalar (-1)^(ab+ba)=1 in every pair of integer degrees. This is the two-line construction of a right-hand tensor map, not a new theorem hidden behind a name.

Step 4 uses the beta/gamma maps on the first two explicitly identified Cartesian squares from Step 1. Its four intermediate objects and the final compositor are typed. `lem-sf-open-tensor-normalization` permits arbitrary unbounded M and N, as do the finite-level clauses of `lem-pur-derived-pullback-tensor-iso`. Thus neither bounded-constructible closure of tensor nor an etale-origin witness has been assumed. Step 5 checks each of these maps under restriction: beta_j, gamma_v, beta_k, the right-extension map and the compositor all restrict to identities by their cited normalization or the earlier calculations. The composition clause of the tensor-pullback node ensures the resulting identification is exactly D.

Step 6 writes the entire opposite-factorization chain, using the right-extension map for the *outer* second factor and the original gamma for the *inner* first factor. The relevant projections are alpha', beta', p, q, not those of the other middle scheme. Its cited normalization theorem applies on these squares too. The restriction calculation uses the same five identity statements, so it proves both isomorphy and the identity restriction for this explicitly defined opposite map.

Step 7 uses the full faithfulness assertion actually present in the normalization node. I checked that it is applied only after the already constructed isomorphism E to u_!D: two arbitrary ambient-source maps cannot be compared by open restriction alone. Conjugating their restrictions by the invertible unit recovers the unique endomorphism of D. This proves equality of the two extension orders without appealing to stalkwise faithfulness or descent for arbitrary derived morphisms.

Step 8 checks the Cartesian swap square by its two projections. The beta for that square is the normalization theorem's actual open base-change isomorphism; after restriction it is the identity. The displayed four projection equalities identify the transported source with H tensor R and its target with u_!(Q tensor P_0), using the composition and signed tensor compatibilities actually stated by the tensor-pullback node. The reversed e is normalized by Steps 1--5 with the typed roles interchanged. Therefore the transport itself restricts to the identity; no unproved general compatibility of compact-support exchange maps is invoked.

Step 9 computes the restriction of the requested composite, including both signs and the naturality of the target unit, before using Step 7's injectivity. Its cited tensor-pullback statement explicitly preserves signed commutativity. In particular the equality uses sigma_(Q,P_0) on the target, exactly as in the item. It is not an assertion that the signed symmetry is always +1.

I tested the identity-open case (both constructions reduce to the given tensor identity), either empty open and zero M or N (both sides are zero), coinciding or disjoint open images, and two odd-degree shifted coefficient complexes. In the odd/odd case each swap is -1, and the two factors in the asserted conjugation multiply to +1; dropping either swap would fail this check when the coefficient ring has odd residue characteristic. The sign argument works also in characteristic two and for unbounded models because only a fixed homogeneous bidegree is involved. All schemes remain k-schemes, so ell is invertible wherever the finite tensor comparison is used. No Tor-amplitude, boundedness, etale-origin, properness of a or b, or abstract datum enters any cited hypothesis.

Every step is shorter than 2000 characters. I inspected the potential hidden subclaims rather than relying on that bound: the right-hand tensor comparison, faithfulness on this source, composition-unit identity, and swap transport are each written out explicitly from existing statements. There is no new clause-restating node, no copied proof standing in for a cited statement, and no newly introduced dependency cycle. The generic open-normalization tool from outside the affine-space unit is declared in split_report.tool_uses; it supplies open operations, not an alternate purity route. I have not set a maintainer-owned reviewed or top-level tool_uses field.
