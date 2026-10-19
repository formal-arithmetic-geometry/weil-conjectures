## Files written

- `dag/nodes/sec-trace-formula/lem-trf-slice-site-base-change-localization.json`: statement unchanged; three proof steps covering continuity, the generic localization theorem after relocalizing at (V/W), and the natural direct-image formula. Mathlib verdict: no exact match for the full site/topos statement.
- `citations.json`: verbatim citations for every node used in every proof step.

## Attachments

No finished declaration exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item. Searches for the item tag, `09W9`, relocalization, and slice-site base change found no project declaration.

## Sources wanted

None. The proof follows `literature/stacks-project/sites.tex`, Tags 03CE and 09W9, which are present locally.

## Audit of the imported node and route

The imported statement agrees clause by clause with Stacks Tag 09W9: the site has fibre products, the right adjoint is fibre-product base change, the induced morphism has the localization geometric morphism, and the direct image is evaluated on the fibre product. I did not add hypotheses on the topology, representability, subcanonicity, or coefficient category. The first draft's proposed adjunction node was removed after the duplicate audit: the existing `lem-trf-slice-subtopos-site-presentation`, applied to the localized site \\(\\mathcal C/W\\) and object \\(V/W\\), already states the needed generic adjunction and direct-image formula.

## Not duplicates

- `lem-trf-slice-site-base-change-localization` vs `lem-trf-slice-subtopos-site-presentation`: the existing node treats localization at an object (U) in an arbitrary site and gives (G(V\\times U\\to U)); this item specializes it to the localized site \\(\\mathcal C/W\\), where the object (V/W) yields the relative fibre product (T\\times_WV), and additionally records continuity of \\(\\beta_f\\) for the original site.
- `lem-trf-slice-site-base-change-localization` vs `lem-weil-pbc-etale-localization-functor-adjoint`: the existing node is only for small étale sites of schemes and an étale morphism; this item is for every site with fibre products and an arbitrary morphism.
- `lem-trf-slice-site-base-change-localization` vs `lem-trf-site-augmentation-acyclic-cech`: the existing node uses Tag 09W9 only as an input to a derived Čech computation for a simplicial site; this item is the underlying arbitrary one-morphism localization statement.
- `lem-trf-slice-site-base-change-localization` vs `lem-trf-slice-site-simplicial-augmentation`: the existing node is the multi-degree simplicial construction and its coherence; this item is the single relative slice-site base-change theorem.
- `lem-trf-slice-site-base-change-localization` vs `lem-sfb-proetale-object-inverse-image-restriction`: the existing node is a pro-étale scheme-specific inverse-image/restriction result with coefficient modules; this item has no scheme, pro-étale, or module hypotheses.

## Review by Q88

I read the item node, the `sk-i-curve-zero` unit, the `sec-trace-formula` chapter, the ancestor `lem-trf-local-term-locality`, and the current blueprint ancestry. I read `sites.tex` at Tag 03CE (localization at an object, its fibre-product right adjoint, and direct image) and Tag 09W9 (all three clauses and the displayed direct-image formula). I also read the full statements of `def-weil-pbc-sites-and-cohomology`, `def-pur-localized-ringed-site`, `def-trf-geometric-morphism`, and `lem-trf-slice-subtopos-site-presentation`. The hypotheses match the item: only a site with fibre products and a morphism (V\\to W) are used.

Step 1 uses the site axiom that a covering remains a covering after base change and the localized-topology clause that coverings are detected on underlying families. Associativity of iterated fibre products supplies the continuity pullback comparison. I checked the empty covering, an isomorphism covering, and the identity morphism.

Step 2 applies the existing localization statement to \\(\\mathcal C/W\\) and \\(V/W\\). I checked the relocalization identification \\((\\mathcal C/W)/(V/W)\\cong\\mathcal C/V\\), the objectwise formula (T\\mapsto T\\times_WV), and the inherited finite-limit and covering conventions. The cited existing node states an adjunction with left exact inverse image and explicitly identifies its geometric morphism with localization, which supplies precisely the item’s second clause after this substitution.

Step 3 is the same existing direct-image formula after the substitution (\\mathcal C:=\\mathcal C/W), (U:=V/W). I checked that an arrow (T'\\to T) over (W) maps to its base change (T'\\times_WV\\to T\\times_WV), and that a sheaf morphism is evaluated componentwise; this gives naturality in both variables. No hidden identification of coefficient categories is used.

The item’s required LeanFinder, Loogle, grep, and LeanSearch searches were run with `msearch.py`; their exact queries and results are recorded in `mathlib_searches` and `searches.jsonl`. They returned only generic over-site infrastructure, so the full site/topos statement remains a non-Mathlib item. I searched the DAG and blueprint for Tag 03CE/09W9 and for slice-localization phrases before deciding that the existing localization node is the correct dependency. Small cases checked: a terminal one-object site, (f=\\mathrm{id}), an empty object, and a two-object site with a nontrivial pullback. In each case the formulas reduce to the ordinary localization/product formulas.

## Unfinished work

Nothing remains unfinished in this one-level split. No Lean source was written and no compiler or build tool was run.

## Validation

The server-side `check_dag` passed. The first dry run caught a citation quote that omitted the opening “Let \\mathcal C be a site…” and the exact parenthetical punctuation; I copied the complete sentence verbatim from `def-pur-localized-ringed-site` into `citations.json`. The repaired dry run passed: `OK (not pushed) deliver/Q88/lem-trf-slice-site-base-change-localization at ff32747334: preflight passed`.
