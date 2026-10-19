## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/det-sp-finite-general-ring.json` — existing item, status changed to `split`; six proof steps retained and checked against the current main-20261015 blueprint.
- `citations.json` — 41 step/node entries with verbatim quotations from the cited DAG statements.

No new DAG node was created. The proof uses the existing `lem-pur-dnc-coefficient-transport` node rather than duplicating it. Mathlib searches for the item were run with `msearch.py` using LeanFinder, Loogle, grep, and LeanSearch; all returned no applicable Mathlib theorem (the returned smooth-algebra and adjunction declarations are unrelated).

Attachments: no sorry-free declaration in `weil-src-slopmaster2/WeilConjectures` states this item. No attachment is claimed.

WANTED: none.

## Source error

The imported blueprint proof paragraph (3) invokes `thm-pur-cohomological-smoothness` directly for an arbitrary finite ring `A`. That theorem is restricted to the DVR quotient coefficients `A_{E,n}`; for example, a general finite ring such as a non-principal square-zero `\ell`-algebra is outside its hypotheses. The item statement itself is retained, but Step 5 replaces that invalid invocation with the ordinary finite-ring tensor theorem `thm-asd-smooth-tensor`, transported through the etale/pro-etale comparison nodes. The report records this correction rather than silently weakening the statement.

## Review by Q81

I read the item source and proof in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.md` and its `.proof.md`, the chapter record `dag/chapters/sec-smooth-purity.json`, and the unit record `dag/units/sk-thm-smooth-purity.json`. The statement in the item keeps the source's three clauses and makes the standing hypotheses explicit: algebraically closed finite-field base, `\ell` invertible, separated finite-type schemes, smooth separated `f` of pure dimension, a finite commutative `\ell^n`-torsion ring, ordinary uncompleted pro-etale module categories, and the specified adjunction and scalar-extension conventions. The source and the item agree on the orientation direction, the direct diagonal/DNC comparison, the tensor map, naturality, and exponent independence.

Step 1 constructs the prime-power orientation and extends it to `A`. I checked the cited statements of `det-sp-reduction-exceptional`, `thm-pur-diagonal-dualizing-object`, `det-sp-scalar-extension-functor`, and `sk-def-sfb-dc-setting`; they provide the coefficient comparison, the prime-power orientation, free Tate-line scalar extension, and the common compactification hypotheses used here. The ring map `R = Z/ell^n -> A` and the unit's bounded constructible finite-Tor hypotheses are explicitly verified.

Step 2 compares the diagonal, deformation, and normal-bundle fibre arrows. I opened `lem-pur-diagonal-base-change`, `lem-pur-dnc-coefficient-transport`, `thm-pur-dnc-invariance`, and `lem-pur-diagonal-regular-immersion`. Their statements give exactly the diagonal section invariant, coefficient/base-change coherence for arbitrary finite rings, normalized DNC comparison, and the diagonal's closed-immersion/normal-bundle facts. The fixed geometric DNC space is separated from the coefficient-dependent family objects, and no section is incorrectly added to the general base-change clause.

Step 3 checks the vector-bundle orientation by its specified integration transpose. I read `cor-pur-vector-bundle-purity`, `def-amb-vector-integration`, `thm-amb-vector-bundle-purity`, `lem-amb-affine-space-top-trace`, `det-sp-reduction-exceptional`, `det-sp-scalar-extension-functor`, `lem-asd-etale-finite-twist-pullback`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `det-ctf-finite-comparison-localizing`, `lem-weil-pbc-derived-single-fully-faithful`, and `lem-pur-sheaf-hom-cover-gluing`. Their statements support the chart counit normalization, local equality, sheaf-map reduction, gluing, zero-section pullback, and passage to the pro-etale realization. The rank, shift, and coefficient hypotheses are checked before applying each comparison.

Step 4 identifies the global prime-power orientation with the global diagonal composite. I checked the statements of `thm-pur-diagonal-dualizing-object`, `thm-pur-cohomological-smoothness`, `thm-pur-dnc-invariance`, `cor-pur-vector-bundle-purity`, `lem-weil-pbc-derived-single-fully-faithful`, and `lem-pur-sheaf-hom-cover-gluing`. The local composites restrict to the affine-cover construction and agree on overlaps; removing the common shift reduces the comparison to sheaf maps, so the cited gluing statement applies. This addresses the earlier gap where a global equality had been asserted without explaining the local-to-global construction.

Step 5 proves the tensor map in the actual arbitrary finite-ring category. I verified the statements of `det-ctf-finite-comparison-whole`, `det-ctf-finite-comparison-localizing`, `sk-prop-sf-existence`, `sk-prop-sf-rf-shriek-preservation`, `thm-asd-smooth-tensor`, `lem-weil-pbc-finite-type-over-noetherian`, `sk-def-sfb-dc-setting`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and `lem-weil-pbc-ringed-exchange-tensor-coherence`. They supply the etale/pro-etale equivalence, adjunction transport, arbitrary finite-ring tensor isomorphism, Noetherian/compactification hypotheses, and preservation of the specified projection map. I checked that the input `K` is in the stated constructible finite-Tor category and that the resulting target remains there.

Step 6 checks naturality and independence of the chosen exponent. I read `lem-asd-etale-finite-twist-pullback`, `det-sp-reduction-exceptional`, `lem-pur-dnc-coefficient-transport`, `lem-amb-kummer-any-base`, `def-amb-p1-trace`, `lem-amb-affine-space-top-trace`, and `def-amb-vector-integration`. The Kummer diagram compares two exponents through a common multiple, and the affine and vector integration normalizations are preserved; the normalized DNC comparison then identifies the direct constructions. Thus exponent independence is established for the specified orientation, rather than inferred from an arbitrary isomorphism of Tate lines.

I inspected all six step texts for hidden sublemmas, including the three steps longer than 2000 characters. Each long step is a single coefficient-comparison, gluing, or exponent-normalization argument whose non-elementary inputs are cited; no additional standalone lemma is hidden. The sole elementary step is Step 4's functorial normalization calculation, which uses only cancellation and the already cited fibre identities. I checked small and boundary cases mentioned by the proof: relative dimension zero, identity and empty schemes, zero coefficient ring, non-flat coefficient maps, square-zero finite rings, and two different annihilating exponents. No duplicate node was introduced, no SGA source was used, and all 41 citation quotes are literal substrings of the current cited statements.

What could not be finished: nothing remains for this stage; the required dry run is the next step.
