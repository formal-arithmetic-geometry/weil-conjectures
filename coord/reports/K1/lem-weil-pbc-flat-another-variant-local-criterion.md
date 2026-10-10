# Review report: `lem-weil-pbc-flat-another-variant-local-criterion`

## Worker report

The worker split Stacks Algebra Lemma 00MO (the another variant of the local criterion for
flatness) into five proof steps.  The auxiliary facts isolated as unsplit nodes are the Tor
surjection after a flat intermediate base change (00MM), the change-of-rings Tor surjection
(00MN), and naturality of the ideal-tensor kernel description (00M6).  No Mathlib declaration
matching any of those three statements was found in the LeanSearch, LeanFinder/Loogle, or
source-grep searches recorded on the nodes.

## Source audit

Before this review I searched the read-only slopmaster2 checkout
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` with `rg` for each item and child blueprint
tag, for the declarations and names in the nodes, and for `Tor`, `surjective`, `local criterion`,
and `ideal-kernel` variants.  No exact declaration was found, and no declaration carries any of
the four blueprint tags.  The closest source is
`WeilConjectures/Mathlib/RingTheory/Filtration.lean`: declarations
`Module.Flat.lTensor_subtype_injective_of_forall_ker` (lines 353--410) and
`Module.Flat.of_flat_quotient_of_lTensor_injective` (lines 528--538) concern relative purity and
the ordinary local criterion, respectively; neither has the 00MO base-change square or any of
the three auxiliary Tor statements.  Therefore these nodes remain split/unsplit DAG work rather
than Lean attachments.  The pre-existing `created.item` chain mechanically points through the
finite-etale-lifting blueprint ancestor; I retained that metadata and recorded its required
`blueprint.from`/`same_as` fields (the blueprint search result is empty).

## Review by K1

I read Algebra Lemma 00MO and its proof at `literature/stacks-project/algebra.tex` lines
23921--23969, together with 00MM (lines 23846--23880), 00MN (23881--23919), and Remark 00M6
(18690--18696).  The item statement has the same commutative square of local homomorphisms,
Noetherian and finite-module hypotheses, proper ideal, localization hypothesis, flat quotient,
and vanishing of the Tor map rewritten as the ideal-tensor kernel map.  The three new statements
are strictly smaller than 00MO and state exactly the corresponding 00MM, 00MN, and 00M6 facts.

Step 1 uses tensor cancellation and the localization hypothesis to identify `M'` with a
localization of `N = M tensor_R R'`; finite generation is preserved by the displayed generators.
Step 2 uses quotient tensor base change and flat base change to identify `N/I'N` with the flat
quotient tensor product.  Step 3 cites both Tor-surjection nodes, the Tor-module structure, the
quotient tensor identity, and the kernel-naturality node; their composite is the required
surjection onto `K_N`, and the hypothesis kills its image.  Step 4 cites exactness and tensor
naturality of localization to identify the localized kernel with the kernel for `M'`.  Step 5
localizes the flat quotient, checks `I'` is proper because the map is local, and applies the
existing local criterion 00ML.  The only elementary parts are the explicitly written balancing,
quotient, and generator identifications; all non-elementary facts have cited nodes.  The listed
`proof_deps` is exactly the union of the step uses.

For the three new nodes I checked B1--B7: each is a self-contained statement, uses TeX for
mathematics, cites every non-elementary notion, identifies the Stacks tag and source lines, has
no proof sketch, and remains `unsplit`.  Existing-node searches on the DAG for the Tor and
kernel statements found no duplicate.  The edge cases `I = 0`, `M = 0`, and a localization at
the identity reduce to the ordinary flat-base-change/local-criterion conclusions and do not
contradict any hypothesis; the proper-ideal and locality checks in Step 5 are necessary.

I added the required blueprint audit fields and this lead review.  No worker proof was changed,
and no exact slopmaster2 attachment was available.
