# Worker report: lem-per-closed-fibre-polynomial-presentation

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-closed-fibre-polynomial-presentation.json`: existing statement node, now split into seven proof steps; no whole-item Mathlib match.
- `citations.json`: sixteen step/dependency entries, each quoting the cited node's actual statement verbatim. This is sandbox validation material.

No new nodes, no new Mathlib leaves, no unit or chapter changes, and no Lean files. The statement is byte-for-byte unchanged from the current repository.

## Attachments

No attachment for the item. Searches of all project `WeilConjectures/` sources for the item id, the blueprint docstring tag and the notions essentially finite type, closed fibre and polynomial presentation found no declaration proving the full item. In particular `AlgebraicGeometry.exists_flat_polynomial_presentation` in `WeilConjectures/Compactification/ValuativeCriterion.lean:293` has an arbitrary family of variables and concerns a flat presentation of a field-valued point; it does not assert a finite polynomial local presentation with a maximal ideal over the base maximal ideal.

The proof reuses the existing attachments `LocalSubring.exists_le_valuationSubring` belonging to `lemma-nagata-local-domain-valuation-dominates` and `ValuationSubring.exists_comap_eq` belonging to `lemma-nagata-valuation-ring-extension`. Both existing nodes have slopmaster2 state `closed`. I read their statements and the latter's project proof at `WeilConjectures/Mathlib/RingTheory/Valuation/LocalSubring.lean:42-64`. This report requests no changes to either node.

## WANTED

None. The source and its valuation lemmas are available in `literature/stacks-project/algebra.tex`.

## What needed correction or expansion

There was no statement error. The item was statement-only and cited the correct Stacks lemma. I read Tag 0AUG, label `lemma-localization-at-closed-point-special-fibre`, statement and entire proof (local file lines 12931-12976). The hypotheses really allow a nonlocal map between local rings; no finite-presentation or Noetherian hypothesis is added.

The split fills four compressions in the source: its reduction from a local ring that is a localization of a quotient; the finite pivot choice expressed there by the value group; the explicit inverse affine-chart substitutions; and the return from the polynomial local ring to the quotient and further localization. These are fraction or finite-induction arguments written in the item's steps rather than new nodes. The source invokes domination inside a field potentially larger than the fraction field of the image of R. To avoid C4, Step 3 uses the narrower existing local-domain domination node only in the image's own fraction field, and then explicitly uses the existing valuation-ring extension node to reach the full residue field.

The ancestor id and via list are preserved. I read the chapter and unit records and the current main-20261015 ancestor statement. The inherited Ratliff algebra branch lies below the unit; its proof source is Stacks 0AUG, and this split changes no unit route or blueprint statement. `blueprint.same_as` is empty after whole-DAG and whole-blueprint searches for the presentation and tag.

## Unfinished work

None in this one-level split. The existing dependencies are reused with their present statuses; no new statement-only obligation is introduced.

## Searches and Mathlib decision

I searched the whole DAG by tag 0AUG and by closed-point, polynomial-presentation, local-domain domination, valuation extension and proper-ideal/maximal-ideal concepts. `tools/blueprint_refs.py ancestor` identifies `lem-per-artin-gabber-affine-curve`; `search` was run for `closed fibre polynomial presentation`, `0AUG`, `valuation`, `local domain` and `valuation ring extension`. The valuation searches expose the two existing domination/extension nodes. The maximal-ideal search finds `lem-weil-pbc-proper-ideal-contained-in-maximal`; all three are reused, not recreated.

All newly recorded Mathlib queries were run through the prescribed `msearch.py` command and retained in `searches.jsonl`; the item's inherited Q04 search records are retained unchanged. This session ran LeanFinder twice with distinct formulations, Loogle with `Algebra.EssFiniteType, IsLocalRing`, grep with `EssFiniteType|closed.fib[er]+|closed.point` in RingTheory, and LeanSearch with the local polynomial-presentation formulation. All services returned results; no unavailable response was treated as absence. I read the returned types and `Mathlib/RingTheory/EssentialFiniteness.lean`, especially lines 40-42, 47-73, 101-110 and 161-166. Its presentation expresses essential finite type as a localization of a finite-type algebra but gives no maximal ideal over the closed point. The formally unramified Loogle hits require additional hypotheses and are not this theorem. Affine-space coordinate and closedPoint hits concern maps of schemes, not the needed existence. The whole item is therefore split, not marked Mathlib.

## Not duplicates

No new nodes. Each ingredient was matched to an existing node. The elementary pivot choice is not a new value-group node; the two chart maps are written in Step 5, not exported as a second polynomial-presentation node.

## Review by Q116

I checked this delivery myself with the source, every cited statement and the written steps open, against delivery-errors B through E. The source of the item is exactly Tag 0AUG (`lemma-localization-at-closed-point-special-fibre`), including its nonlocal-map parenthesis. I also read Tag 00IA (`lemma-dominate`), Tag 00IB (`lemma-valuation-ring-x-or-x-inverse`), Tag 00ID (`lemma-valuation-group`), and the localization fraction definition and Tag 00E3 (`lemma-spec-localization`). The tag mapping was read in `literature/stacks-project/tags/tags`. There are no new node sources to review.

Step 1 uses `def-weil-pbc-essentially-finite-type-algebra` for the actual multiplicative localization and its equality rule, `def-weil-pbc-finite-type-algebra` for the surjective finite polynomial presentation, and `def-weil-pbc-localization-at-prime` for fractions at the contracted prime. Each quoted statement says exactly that. The kernel contains I, the maximal ideal of S contracts to a proper prime, and every denominator in W maps to a unit, so the surjectivity and injectivity calculations apply. This is an elementary universal-property and fraction calculation, not an invocation of an uncited local-presentation theorem.

Step 2 invokes precisely the assertion of `lem-weil-pbc-proper-ideal-contained-in-maximal`, and explicitly establishes its proper-ideal hypothesis. No assertion that a maximal ideal contracts to a maximal ideal for an arbitrary ring map is used: contraction contains the already maximal m_R and is proper. The localization statement is proved with the fraction definition in `def-weil-pbc-localization-at-prime`. This step is marked non-elementary because existence of a maximal ideal is cited as a theorem.

Step 3 uses `def-weil-pbc-localization-at-prime` to construct the field kappa(q). The image B of the local base is a quotient by a proper prime, hence a local domain. I checked that `lemma-nagata-local-domain-valuation-dominates` requires the fraction field of B, so it is applied there, not immediately in kappa(q). `lemma-nagata-valuation-ring-extension` then supplies the extension along that genuine field inclusion and explicitly says the larger valuation ring dominates the smaller one. Successive contraction gives the exact maximal ideal required. These are the only non-elementary valuation-existence results used, and both statements are cited. The nonlocality of R to S causes no difficulty: the image R to kappa(q) is still a quotient of R.

Step 4 uses the full either-x-or-inverse membership clause of `def-trf-valuation-ring`, which is in its statement, and polynomial evaluation from `def-weil-pbc-mv-polynomial-ring`. I wrote the pivot induction instead of citing the definition for total ordering of the value group, which it does not state. The pivot is nonzero; division is never by a zero coordinate. Keeping a pivot preserves prior ratios, and replacing it multiplies every prior ratio and its inverse by an element of A. Thus a finite list suffices, with no hidden value-group existence lemma.

Step 5 uses only the polynomial universal property and the concrete fraction construction in the two named definition nodes. Both coordinate substitutions, their compositions, and the test of transformed denominators in kappa(q) are written out. I checked that y_0 is outside q_Q because its value is the nonzero inverse of the pivot. The substitutions fix R, so the resulting local isomorphism preserves the R-algebra structure needed when the quotient is transported.

Step 6 uses the same two definition statements: evaluation factors through A because every generator and coefficient lands there, and the residue-field kernel is exactly the maximal ideal of the prime localization. The preimage of m_A contains both q_Q and m_RQ and is proper. This supplies Step 2's hypothesis without any unproved closed-image or properness assertion.

Step 7 uses the multiplicative-localization and fraction definitions of `def-weil-pbc-essentially-finite-type-algebra` and `def-weil-pbc-localization-at-prime`. The ideal is transported along the actual R-algebra isomorphism of Step 5. Contraction then extension recovers it because multiplication by an inverted denominator returns the numerator to the contracted ideal. The quotient fraction map is consequently an isomorphism, with the same cross-multiplication rule; this is the short direct quotient-localization calculation, not another node. The maximal ideal already lies over m_R by Step 2.

For edge cases I checked a field base (m_R=0, so the first case suffices), n=0 (q lies in m_R, again the first case), a non-domain base (B is still the domain R/p), nilpotent elements in the initial quotient (the equality-of-fractions test needs no domain hypothesis), zero coordinates (retained without inversion), and a nonlocal map with empty special fibre in the original chart: R=k[t]_(t), S=k(t), presented by P=R[x] and q=(tx-1). Then q+(t)=P, while the change y=1/x gives q_Q=(y-t) contained in (t,y); taking the quotient by y-t after localizing at (t,y), and then inverting y, recovers the original field presentation. This checks why insisting on the original polynomial prime would be wrong and why the new chart succeeds. The zero ring itself is excluded by the item's definition of a local ring as having exactly one maximal ideal, so no unsupported zero-ring exception is imposed.

I checked B1-B9 without creating nodes: every used notion has an existing definition or an explicit local description; JSON uses single TeX escapes; the statement never depends on a tag for its meaning; sources give labels and tags. For C1-C4 every non-elementary fact used is in the statement of a cited node, and the sixteen exact quotations in citations.json are still verbatim in the current shared DAG. C5 and D1-D2 were checked by reusing existing nodes and putting the actual argument in the item. The new proof edges go only to existing definitions, closed valuation results and the maximal-ideal leaf; none requires this item. Both non-elementary steps have fewer than 2000 characters, and every other step also has fewer than 2000 characters. No SGA source, no source dispute, and no target statement change is involved.
