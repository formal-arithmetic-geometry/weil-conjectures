# Stage-1 report: lem-pur-finite-triple-product-normal-forms

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-triple-product-normal-forms.json`: item split in five steps; not a Mathlib leaf.
- `citations.json`: 15 verbatim statement quotations, one for each citation in each proof step.
- `searches.jsonl`: actual searches logged by the required search command. The item's inherited searches are retained; five searches made by Q39 are added to the item.
- New nodes: none. Mathlib leaves created: zero.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for triple products, product compactifications and normal forms. `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp` in `SixFunctors/Etale/Derived/KernelTransform/Finite.lean` concerns composition of kernel transforms on the small etale site, and does not state either specified normal-form equality. Its existence therefore is not an attachment of this item. No compiler or build tool was used.

## Wanted literature

None.

## Corrections and scope

The item statement is unchanged. The source gives compactification reduction tersely; the split writes out how two binary reductions give each triple identity, including the naturality equation needed to move the inner open comparison through the outer ordinary word. No associativity of the actual forward product is assumed, and the split never identifies the two proper triple words with each other. That identification is a separate existing node used by the parent.

The abstract nodes `lem-sf-triple-compactification-normal-form` and `lem-sf-product-compactification-identity` cannot be applied here: they assume an abstract six-functor datum and finite-Tor constructible inputs. The concrete node `lem-pur-finite-product-compactification` already states the needed binary result on bounded-below etale-origin inputs without either assumption. The item is an elementary assembly of that non-elementary binary theorem, not grounds for duplicating it.

All work is stage 1. Only the assigned sandbox was written. The repository and launcher are unchanged.

## Unfinished work

None in the assigned one-level split. The cited nodes remain responsible for their own statements.

## Not duplicates

No new nodes were created. DAG keyword searches found both abstract compactification normal-form nodes and the concrete binary node. `tools/blueprint_refs.py search` found no imported node for 'triple compactification'; the whole-blueprint search for 'external product' returned eight imported nodes, none stating these two separate concrete identities on the item's domain. The nearest imported ancestor is `prop-pur-affine-space-composition-law`.

## Review by Q39

I read `GOAL.md`, the stage-1 brief, the chapter and unit records, the three levels in SETUP, and both copies of delivery-errors B--E in full. I read the current blueprint through `literature/blueprint/latest/`, whose snapshot is 2026-10-23-1620 (7284bb09). In particular I read the affine-space composition proof Steps 3--4, the corresponding current unit and chapter, and the entire relative-product coherence proof. The latter proposes compactification reduction but does not itself prove the finite witnessed-domain statement. Accordingly this proof is marked agent-written, with that current source and the precise clauses it elaborates. No chapter or unit route was changed. There are no new nodes requiring independent sources.

For Step 1 I opened the statements of `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-proper-fp-permanence` and `def-pc-fibre-product`. The first really states that the product of the opens is open, and the second supplies both proper base change and proper composition. In the Stacks source I read Tag 01JR, label lemma-open-fibre-product in schemes.tex, and Tags 01W3/01W4, labels lemma-composition-proper/lemma-base-change-proper in morphisms.tex. The base open is all of B, so there is no hidden image-containment hypothesis. The universal property gives the product reassociations by their projections, without invoking associativity of a sheaf product.

For Step 2 I read `lem-pur-finite-open-product-swap`, including its unrestricted unbounded finite-coefficient domain and its assertion that the actual maps restrict to identity. I also read `lem-pur-derived-pullback-tensor-iso`, including its naturality and associativity/composition clauses, and `lem-cbc-extension-zero-composition`, which supplies the natural open compositors. I checked the current blueprint text for the last node and read Stacks Tag 07A4, label lemma-pullback-tensor-product. Pullback/tensor of identity maps remains identity, so the two iterated e maps each have exactly the claimed normalization. This step needs no comparison of e_L with e_R and no descent of arbitrary derived morphisms from an open restriction.

For Steps 3 and 4 I read the entire statement of `lem-pur-finite-product-compactification`, comparing its T word arrow by arrow with Xi and its Omega word with the item's proper word. They agree, including the two signed symmetries and the inverse ordinary direct-image compositor. Its hypotheses are finite coefficients, separated finite-type geometry, bounded-below inputs with etale-origin witnesses and witnessed bounded-below tensors in the forward word. The item explicitly assumes the corresponding conditions for every binary and iterated word; thus D_12 and D_23 are legal outer inputs. The extension objects H_12 and H_23 need no new preservation theorem here: the binary theorem itself produces them, and Step 2 supplies their identification with E_12 and E_23. Naturality moves the isomorphisms e_12 and e_23 through the outer proper words, in the first and second variables respectively. To justify that claim I read `def-exchange-projection`: its exchange, projection and chosen-compactification maps are specified natural transformations, not invertibility assertions. I read the full `lem-weil-derived-direct-image-composition` statement and its current blueprint text: its compositor is natural and exists on all finite-level unbounded inputs. Both naturality squares are written explicitly in the proof, so no hidden product-associativity or unspecified transport lemma is being cited. The compositor is declared as a generic tool use from its own unit; there is no replacement of the affine-space route.

For Step 5 I checked the last paragraph of the binary lemma: it explicitly allows any original compactifications and any displayed compactifications under normalized comparisons. I separately read `thm-sf-comp-composition`, whose statement gives choice independence and associativity on the bounded-below etale-origin class, and the full `prop-compactification-coherence-detailed` statement, whose finite-common-refinement and cocycle assertions have precisely the same etale-origin restriction. The item's witnesses meet that restriction. I derived refinement compatibility by transporting each equality to the same Xi iterate; it does not follow merely from the existence of isomorphisms of the underlying functors. The choice-independence assertion of the binary lemma is the essential cited input.

I tested the formula on identity opens (all e maps become identity), already proper maps (choose identity-open compactifications), empty factors (both sides have zero target), and a zero coefficient complex. I also checked why finite Tor amplitude cannot be inferred from two bounded-below inputs and did not infer it: the explicit tensor-domain hypothesis is retained. Arbitrary n, including nonfield A, is allowed by the binary and open lemmas; no flatness or invertibility of exchange/projection was added. All five non-elementary steps are below 2000 characters; none hides a new lemma with separate hypotheses. The underlying binary comparison already exists, so creating left and right normal-form nodes would only duplicate the item's clauses (D1/D2).

I checked B--E against the final JSON: every object is introduced, the statement and inherited metadata are preserved, mathematical text is single-escaped after JSON decoding, no new statement-only node contains an inline proof, and every non-elementary input is a cited statement. I verified every citations.json quote as a literal substring of its cited live node's statement. The 15 entries cover the union of the five uses lists, and proof_deps is exactly their union. No statement dispute or missing hypothesis was found.

I ran LeanFinder twice with different semantic phrasings, LeanSearch once, Loogle once and the required Mathlib grep. I read every returned signature. The first semantic search returned light-condensed monoidal structures and sheaf cartesian closedness; the second returned ordinary SheafOfModules pushforward compositions and their components. I opened the relevant Mathlib files (Condensed/Light/Monoidal.lean and Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean). These do not state compact support product identities on the pro-etale derived category. LeanSearch returned compact-support functions and finite categorical products; Loogle and grep returned no hits. The exact queries and actual outcomes are recorded, with no unavailable service described as an empty search.

## Dry-run repair

The first server preflight rejected Step 3 because the phrase “the item's hypothesis” is not self-contained wording. I replaced it with the explicit assumed bounded-below etale-origin condition on the tensors in the iterated forward words. The mathematical hypothesis and statement are unchanged.
