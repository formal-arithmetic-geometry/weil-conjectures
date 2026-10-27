# Q58 stage-1 delivery: lem-trf-diagonal-taylor-faithful-flatness

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-diagonal-taylor-faithful-flatness.json`: statement node, now split in eight steps; no full-item Mathlib match. All hypotheses and conclusions are unchanged. The existing blueprint reference and historical provenance are retained.
- `citations.json`: one entry for each use in each proof step, with verbatim statements from the existing cited nodes.
- `searches.jsonl`: five real msearch queries, with results read; no unavailable service in this run. The existing item's earlier recorded searches are retained.
- `report.md`: this report. `write_split.py` is a sandbox helper, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. Every substantive input already exists; creating a second node for any of these would violate the duplicate rule.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact item id/blueprint tag, Taylor, diagonal completion and the underlying coordinate notion found polynomial Taylor expansions and the smooth-augmentation construction, but no declaration proving all the present residue-diagonal, quotient, faithful-flatness and arbitrary-field-extension clauses. Upstream sorry declarations were not treated as finished proofs.

## Wanted literature

None. The relevant Stacks sources are present. No SGA source is used.

## Corrections and observations

No statement correction or dispute. The supplied node was unsplit, and the sandbox had no earlier node/report. The proof now realizes all clauses rather than moving them into new clause nodes. Its general infinitesimal input is the existing `lem-sfb-augmented-etale-associated-graded`, not a new Taylor-specific quotient lemma. Its completion input is the existing `lem-trf-etale-chart-rational-point-taylor-iso`.

I read the chapter/unit records, the current `literature/blueprint/latest/` unit and local-term-locality statement/proof (snapshot main-20261023-1620), the item and its coordinate-calculus parent, and the three levels in SETUP. The ancestor's nearby-cycle/alteration branch is historical, as the inherited reference says. This local algebra input does not change a chapter or unit argument, and does not introduce a trace theorem or replace the current contracting-correspondence route.

The existing affine triple tensor comparison and the formally etale quotient comparison are declared generic tool uses in `split_report.tool_uses`. The former identifies the actual chart arrow after base change, including tensor factors; the latter identifies the actual quotient maps and states their naturality. Neither is a replacement for a unit proof step. All other off-unit statement citations are Mathlib leaves, or are in the item's own unit.

## Unfinished work

None for this stage-1 item. No Lean was written or compiled. Server dry-run and push results follow below when available.

## Not duplicates

No new nodes were created. Before deciding that, I searched the whole DAG by tags 0H1D, 00MC, 00HR, 00HT, 02GO, the formal-etale lifting label, and by Taylor, completion, rational-point and flat-local concepts. Whole imported-blueprint searches were run using `tools/blueprint_refs.py search` for Taylor, formally etale, polynomial completion, power series, completion, infinitesimal and rational point, and the ancestor command was read. The existing general quotient node and rational Taylor-isomorphism node give separate inputs, while neither is the whole item (the former has no faithful-flat Taylor map; the latter has no arbitrary original residue-field point or field-extension compatibility). No new polynomial-completion node is needed.

The five new Mathlib queries use the item's id in their natural-language queries and are recorded exactly as run. Loogle found `MvPowerSeries.toAdicCompletionAlgEquiv` and its coefficient formulas, which identify polynomial completion only. LeanFinder found standard smooth charts and, on the second phrasing, `Module.FaithfullyFlat.of_flat_of_isLocalHom` and `RingHom.Flat.localRingHom`. LeanSearch found one-variable Laurent-series completion equivalences and `RingHom.FormallyEtale`. The grep for Taylor/flat and etale/completion found nothing in RingTheory. These are constituent inputs, not an exact theorem or a one-line specialization giving this item's conjunction and canonical maps. Existing Mathlib leaves for the flat-local and completion facts are reused rather than recreated.

## Review by Q58

I read delivery-errors B through E in both copies, then checked the statement and each proof step against the actual cited statements. The Stacks texts read were algebra.tex Tags 0H1D (lemma-formally-etale-lift-infinitesimal), 00HT (lemma-flat-localization), 00HR (lemma-local-flat-ff), 00FN (lemma-Noetherian-permanence), 00MC (lemma-completion-faithfully-flat), and Section 00M9 (section-completion); morphisms.tex Tags 02GJ (lemma-etale-characterize) and 02GO (lemma-base-change-etale); schemes.tex Tags 01I4 (lemma-fibre-product-affine-schemes) and 01JR (lemma-open-fibre-product); and etale.tex Tag 039M (lemma-characterize-etale-completions) with its residue-degree remark. I also read the affine stalk and formal-power-series definition nodes. There are no new-node sources to certify.

Step 1 uses `lem-a1-etale-open-restriction` for restricting the original etale chart, `lem-weil-pbc-etale-scheme-base-change` for its extension to L, and `lem-weil-pbc-affine-triple-tensor-base-change` for the coordinate ring and induced arrow on the pulled-back affine open. The last node explicitly allows arbitrary base change and gives the actual tensor-product ring homomorphism. I checked its opens and affine charts with S=Spec k, Y=A^n_k, X=U and T=Spec L. Swapping tensor factors and translating variables use the displayed formulas and the polynomial universal property in `def-weil-pbc-mv-polynomial-ring`. The augmentation has a section from L, so its quotient is L; the polynomial kernel is precisely the zero-constant-term ideal. This verifies every hypothesis of the quotient lemma in the next step.

Step 2 uses `lem-sfb-augmented-etale-associated-graded` only for what its statement explicitly supplies: the canonical isomorphisms A/I^q -> C/J^q, the sufficient etale hypothesis, and naturality under compatible ideal-preserving maps. I checked that its A is P here, not the original affine algebra A, and that the composite P -> C/J is surjective with kernel I. There is no implicit assertion that J=IC. Its associated-graded conclusion is unused.

Step 3 is the explicit elementary localization calculation using `def-weil-pbc-localization-at-prime`: a denominator outside J has a nonzero scalar residue, hence the displayed finite geometric series is its inverse modulo J^q. The denominator-clearing argument proves the kernel equality as well as surjectivity; no exactness theorem or unproved localization/quotient comparison is being quoted. It works even if the affine scheme has other connected components. The maps are reductions of the same fraction map, so compatibility is verified, not asserted without a formula.

Step 4 uses `lem-weil-pbc-affine-open-stalk-localization` to identify C_J with the actual stalk and `lem-trf-etale-chart-rational-point-taylor-iso` with exactly its stated rationality hypothesis. The point is b_L, whose residue field is L by the augmentation; it is not an assertion that b is L-rational in the original scheme. The existing Taylor-isomorphism lemma states the finite truncation formula, uniqueness and the n=0 case. I compared that formula to the maps of steps 2 and 3. `def-weil-pbc-adic-completion` states that the completion consists of compatible quotient sequences, so agreement on projections gives the inverse-limit identification claimed here. No arbitrary choice of a Cohen isomorphism is used.

Step 5 uses `lem-weil-pbc-field-extension-base-change-faithfully-flat` for A -> A tensor_k L. Its statement permits arbitrary commutative k-algebras and arbitrary field extensions. The contraction of J is exactly p by evaluation, so `lem-weil-pbc-flat-local-ring-maps` supplies the correct localized flat local homomorphism. The first sentence of `lem-pc-local-flat-faithful-flat-reflects-surjective` states that such a map is faithfully flat. The affine stalk node identifies this concrete fraction map with the morphism of local rings of U_L -> U. No completion or residue-field algebraicity assumption is smuggled into this step.

Step 6 verifies Noetherianity before applying completion faithful flatness. `lem-weil-pbc-etale-algebra-finite-presentation-localization` states that C is finitely generated over P. `lem-weil-pbc-finite-type-algebra-noetherian` applies twice, first to the finite polynomial algebra over the field L and then to C; the field's two ideals prove its Noetherianity directly. `lem-weil-pbc-localization-noetherian` gives Noetherianity of C_J. Therefore `lem-weil-pbc-local-completion-faithfully-flat` has precisely its Noetherian-local hypotheses. Composition of faithful flatness is written out using the tensor-exactness definition in `def-weil-pbc-faithfully-flat-ring-map`, so no uncited permanence theorem is needed.

Step 7 uses the affine stalk node for independence of the affine neighbourhood and the compatible-sequence completion definition for equality after completion. The stalks and germs are the same intrinsic stalks, and the map on each series is determined by its polynomial truncations in that same stalk. The fraction constant term a(b)/s(b) is defined because s is outside p. The coordinate formula and augmentation calculation are those already proved in step 4, not properties taken from the proof of a cited node.

Step 8 checks field-extension compatibility explicitly: epsilon_K composed with h equals the coefficient inclusion composed with epsilon, so h^{-1}(J_K)=J and all the local maps exist. The polynomial square commutes on constants and variables. The naturality clause of `lem-sfb-augmented-etale-associated-graded` supplies the quotient square, and the displayed fraction inverse from step 3 supplies the localized square. `def-weil-pbc-adic-completion` then supplies the coordinatewise completed map. The finite truncation formula identifies it with coefficient extension of formal series. This avoids a false identification of a completed tensor product with the ordinary tensor product L[[X]] tensor_L K. Repeating steps 1--4 over K is justified for the same etale chart and its induced K-rational point; no finiteness of K/L is assumed.

Small cases checked: q=1 gives the identity of the residue field. For the generic point of U=A^1_k, L=k(t), J=(t-t(b)) in L[t], and t maps to t+X; denominators from k[t] nonzero at the generic point have invertible constant term. This checks the nonclosed-point clause and rules out incorrectly completing A_p itself. For n=0 an etale zero-dimensional chart has the diagonal local ring L, as the cited rational lemma explicitly states; every truncation and coefficient map then reduces to the field map. For an etale chart with several components, the geometric-series argument still works without globally identifying J with the coordinate-generated ideal. In positive characteristic no factorial, derivative expansion or characteristic-zero hypothesis is used. For a transcendental extension K/L the same quotient square and coefficient formula remain valid.

I checked B1--B10: no unsplit new node, no incomplete statements or invented notion, TeX escaping unchanged, precise Stacks labels, existing Mathlib leaves reused, genuine search records, completed blueprint field, and no attachment claiming sorried Lean. For C1--C8 I opened every cited statement, recorded a verbatim quote for each step/node pair, checked the exact hypotheses above, checked no dependency path returns to this item, and declared the two generic off-unit tools. For D1--D5 the argument is carried by eight steps and creates no clause-restatement node. For E1--E7 I verified the residue fields, actual localizations, inverse formulas, completion maps and field-extension square. All eight steps are below 2000 characters; there is no long step hiding an unrecorded comparison lemma. There was no mathematical correction to the imported statement.

## Server validation

`review_split` completed successfully on the server: PASS, 0 new nodes. The full `deliver.py --no-push` invocation then exited 0 with `OK (not pushed)` at b2026833215; server preflight passed. The unit realization warning refers to the unit's unstamped key node, which this local supporting lemma does not own. No local DAG/preflight checker, Lean compiler, Lake command, repository write or repository git command was run.
