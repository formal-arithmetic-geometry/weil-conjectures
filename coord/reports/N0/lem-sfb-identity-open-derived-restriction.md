## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-identity-open-derived-restriction.json`: statement, split into six steps; no exact Mathlib match. Original statement, statement dependencies and original searches retained; fresh logged searches appended.
- `citations.json`: fourteen entries, one verbatim statement quotation for each step/node citation.
- `report.md`: this report. `write_split.py` is sandbox-only preparation; `searches.jsonl` is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, identity/open restriction, and composition/direct-image restriction terminology. The Zariski structure-sheaf theorem `AlgebraicGeometry.open_derived_restriction_comparison` in `AlgebraicGeometry/OpenDerivedRestrictionComparison.lean` does not assert this comparison for pro-etale internal condensed modules, nor this coherence equation. The etale lower-shriek compactification coherence is likewise in a different category and has different hypotheses. No attachment is claimed from a declaration with sorry or from a partial match.

## WANTED

None. The Stacks sources needed for the argument are present.

## Errors and corrections

The item had an empty proof. Its statement is correct and is unchanged. The split supplies the actual section maps and computes both the composition and identity laws; it does not replace the item or one of its clauses by a new node. There is no statement dispute.

The current source is main-20261015, `sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle.proof.md`, Refinement isomorphisms and Independence. I read the chapter, current unit text, parent node and its proof. The unit record `dag/units/sk-prop-sf-comp-coherence.json` retains the older master chapter path and statement; the current blueprint has the unit in six-functors-basics, as the item's chapter already records. I follow the current blueprint, and change neither the unit nor its realized fields because this item is not the unit's key statement.

The related existing node `lem-sfb-base-change-identity-open-restriction` includes a restriction comparison but assumes separated finite-type schemes over a field; it cannot justify the present arbitrary-scheme statement. Its proof was read for comparison, but it is not used. The existing compositor node is used only for the normalization it explicitly states. No parent or dependent normalized-refinement node is cited, so the argument is not circular.

## Unfinished work

No mathematical part of this one-level split remains. Statements of the existing cited nodes remain their respective owners' obligations. No Lean was written and no compiler, Lake or build tool was run.

## Review by N0

I read delivery-errors B–E in full and checked the split against those cases with the cited statements open. The supporting primary sources read were Stacks Tag 03CE (`sites-lemma-localize-given-products`); Tag 0D6G (`sites-cohomology-lemma-restrict-direct-image-open`) and Tag 0D6E (`sites-cohomology-lemma-derived-pushforward-composition`); Tag 08BJ (`derived-lemma-adjoint-preserve-K-injectives`); Tag 070I (`derived-lemma-K-injective`); Tag 079P (`injectives-theorem-K-injective-embedding-grothendieck`); and the ringed-module definitions and adjunction, Tags 03D6/03D7, together with `sites-modules-lemma-localize-morphism-ringed-sites`. I also read Tag 08FI's K-injective restriction argument as a cross-check, but the split does not need to cite or apply it: exact open pullback acts on an arbitrary representing complex, and we do not assert that its restriction must be K-injective to construct r_h. The blueprint contributes the compactification-coherence purpose; the explicit normalized calculation is marked agent-written.

Step 1 uses only clause (1) of `lem-weil-proetale-weakly-etale-localization` for equivalence of the small open sites and slices. Its constant-ring clause is not applied to condensed coefficients. `lem-sfb-internal-module-operations-transport` explicitly compares the module functors by exact equivalences; `def-pur-localized-ringed-site` explicitly gives evaluation and restriction of ringed modules. `sk-prop-sfb-cartesian-coefficients` explicitly gives the untwisted coefficient isomorphism and exact module pullback for arbitrary schemes. Thus the passage to sectionwise modules and the coefficient actions are justified, without substituting constant coefficients, completed categories, or constructible categories.

Step 2 uses the definition of open immersion to identify the entire preimage open, not merely a set of points. The inverse map (1_V,j'v) and both composites are written explicitly. `def-sfb-finite-lower-star` states the needed evaluation formula, and `sk-def-sfb-module-pushforward-pullback` states the action through the adjunct structural ring map. Under the stipulated pullback-from-point identifications that map on the localized identity is the identity. The same maps commute with all arrows over U. This is an elementary calculation from these constructions, not a geometric base-change theorem assumed without a citation.

Step 3 uses `prop-pur-kinjective-resolutions-exist` on the small ringed sites; exact equivalences from step 1 preserve the defining homotopy vanishing, so those resolutions also exist for internal modules. `sk-def-sfb-module-derived-pushpull` explicitly computes the total unbounded direct image on these resolutions. `lem-weil-pbc-kinjective-hom-derived` states the Hom bijection needed for morphisms, resolution independence and naturality. It supplies more than full faithfulness of an unrelated embedding. Exact pullback is used to identify the target restriction on the chosen representative; no boundedness hypothesis is introduced.

Step 4 checks both hypotheses of `lem-weil-pbc-right-adjoint-preserves-kinjective`: the module adjunction is explicitly in `sk-def-sfb-module-pushforward-pullback`, and exactness/additivity of its left adjoint is supplied in step 1. Thus k_*I is an admissible K-injective representative when computing r_h at Rk_*K. No claim that arbitrary ringed-topos pushforward preserves K-injectives is made; the exactness hypothesis is essential here and verified.

Step 5 uses the actual statement of `lem-sfb-module-derived-compositor-coherence`, namely that kappa is the inverse of the termwise module compositor on K-injectives. After step 4, all terms can be calculated on the same I. Both inverse fibre-product maps have projections (1_V,j''v), so the universal property proves equality before localization. This proves the prescribed natural-transformation equation, including associators and coefficient identifications, rather than merely exhibiting isomorphic endpoints. The composite hk again satisfies both open conditions, as the preimage equation in the step shows. Step 6 uses the same node's explicit sectionwise identity normalization; it does not substitute an arbitrary isomorphism R(id)_* ≅ id.

All non-elementary inputs are existing cited nodes. Statements were checked individually, and the fourteen quotations in citations.json are verbatim substrings, including the exact preservation and normalization assertions. Off-unit generic tools are declared in split_report.tool_uses with their reasons. The steps are all shorter than 2000 characters. No non-elementary comparison has been hidden in a long step.

Edge cases checked: U empty gives the zero restriction category and the same unique maps; U the whole base forces h to be the given identity identification and gives the direct-image equivalence; h or k identity gives the canonical unit normalization; the zero complex gives the unique zero comparison; arbitrary unbounded complexes are covered by the small-site K-injective theorem; arbitrary schemes and all admissible condensed coefficients are allowed since neither localization nor untwisted pullback exactness assumes a field, properness, density, or Noetherian hypotheses. The assumption that the entire inverse-image open is j'(U) is used explicitly, preventing extra components over U.

I searched the whole DAG and blueprint by open restriction and identity-over-open terminology (blueprint_refs search), and read the related more restrictive existing statement. No new node is needed, so duplicate/tag-pair checks for new nodes are vacuous and blueprint.same_as remains empty. Fresh logged leanfinder, loogle, grep and leansearch queries, and a second semantic phrasing, were read. The plausible hits were underived Zariski O_X-module restriction/composition; I read Mathlib/AlgebraicGeometry/Modules/Sheaf.lean around lines 390–460. None states this unbounded pro-etale module-object result in one specialization. The source matches and old search history are retained.

## Not duplicates

No new nodes were created.
