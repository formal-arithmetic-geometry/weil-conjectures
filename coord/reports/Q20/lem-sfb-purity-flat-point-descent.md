# Q20 — lem-sfb-purity-flat-point-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-purity-flat-point-descent.json`: statement, split into seven steps; not a Mathlib leaf. The imported statement and its statement dependencies are unchanged.
- `citations.json`: 24 verbatim statement quotes, one for every use in each step.
- No new nodes and no new Mathlib leaves. An interrupted exploratory draft for pointwise flat generalization lifting was removed: the short local-spectrum reduction is step 4, using existing nodes. The saved searches and original root copy remain available in the sandbox; only `dag/nodes/` files are delivery inputs.

## Attachments

None. The project library was searched for the exact blueprint tag, relative purity, impurity, and flat lifting. No sorry-free project declaration states the item. Uses of `Flat.generalizingMap` in the library assume global flatness and do not state this result.

## WANTED

None. The proof source is present: Stacks Project `flat.tex`, Tag 05J9, `lemma-flat-descend-pure`, assertion (1). I also read its impurity and purity definitions (05IY, 05J4), Morphisms 01U8/01U9 and 03HV, Algebra 00HS, Schemes 01JT, and Divisors 05DC. No SGA source is used.

## Findings and changes

The item was unsplit. Its statement agrees with Tag 05J9(1); in particular flatness is only at the distinguished point, and the base-change residue field may be any extension. The source's initial assertion of a unique point above the two chosen points is only needed here for an elementary etale neighbourhood, where the original residue field map is an isomorphism. The proof explicitly constructs the needed point by a field-valued point and proves the new residue-field isomorphism by a field retraction. It does not repeat the uniqueness claim for an arbitrary impurity.

The inherited blueprint provenance and unit were preserved. Whole-blueprint searches by purity/flatness, generalization and going down, together with inspection of `literature/blueprint/latest/`, found no blueprint node restating this item; `same_as` is empty. The item's ancestor command reports no blueprint ancestor. The existing route through purity and proper-support prerequisites is retained. Generic tools outside the unit are declared under `split_report.tool_uses`: quasi-coherent pullback, finite-type module pullback, canonical local spectra, and relative-assassin base change. No top-level maintainer-owned tool field was added.

Mathlib searches already logged in `searches.jsonl` were read and reused. The initial and second phrasings give flatness, going down and generalizing-map results, but no impurity-based relative-purity descent theorem. The imported search history is retained, and exact additional logged queries are recorded. The exploratory pointwise-lifting search also remains in the log; it did not justify a new node once the existing local-spectrum and affine-flatness statements were combined.

## Unfinished work

None in stage 1. No Lean was written and no compiler, Lake or build was run. Server dry-run results and delivery commit are supplied by the required delivery command.

## Not duplicates

No new nodes. I reused the existing field-tensor nontriviality, maximal-ideal existence, component-cover, sobriety, fibre-product-points, pointwise module-flatness and relative-assassin nodes instead of introducing specializations of them.

## Review by Q20

I checked the proof against Tag 05J9(1), not against an imported proof sketch. The seven steps retain its contrapositive route: an elementary-etale impurity downstairs is lifted to an elementary-etale impurity upstairs. Each step is shorter than 2000 characters.

Step 1 uses `def-sfb-scheme-relative-purity` for exactly the impurity data and the residue-field condition of an elementary etale neighbourhood. `lem-sfb-finite-type-composition-base-change` gives finite type of each base-changed morphism, and the two existing module pullback lemmas give quasi-coherence and finite type. Their statements impose no finiteness or Noetherian assumption on the base change.

Step 2 uses the field-valued-point bijection and the fibre-product universal property to construct the point over t and s'. The residue-field definition gives the induced field maps. Their composite is the identity; injectivity of a map of fields shows the two maps are inverse. The etale-base-change node gives etaleness, and the purity definition then gives the elementary neighbourhood condition. The only residue-field isomorphism used downstairs belongs to (T,t), never to (S',s').

Step 3 uses clause (1), not clause (2), of `lem-sfb-pointwise-module-flatness-base-change`. I specialized its source scheme to S', its base to S and its module to the structure module. The hypothesis is exactly O_{S',s'} flat over O_{S,s}; the pullback definition identifies the resulting module with O_{T1}. Thus the resulting flatness is at t1, not an unjustified global-flatness assertion.

Step 4 uses the statement of `lem-weil-pbc-spec-local-ring-canonical-morphism` for its image being all generalizations and for its explicit description by germ maps. `lem-weil-pbc-flat-ring-map-iff-flat-affine` makes the flat stalk map into a globally flat map of local spectra. Only that map is passed to `lem-weil-pbc-flat-generalizations-lift`. The closed points map correctly since the stalk map is local. Canonical-spectrum commutation follows by the displayed germ-ring maps. Thus the new point generalizes t1 and maps to t'. This is a short specialization of the cited statements, not a hidden generalization theorem requiring a separate node. I replaced the interrupted draft node with this argument and avoided its ambiguous verbal specialization convention.

Step 5 uses the field-tensor node for two genuine extensions of kappa(t'), the nontrivial-ring maximal-ideal node for a point, the component-cover node for a component containing that point, and the scheme-sobriety node for its generic point. The fibre-product-points statement identifies the residual prime with a point over both xi and t1'. Hence existence of the generic lift is justified even without Noetherianity.

Step 6 uses the full equivalence in `lem-trf-relative-assassin-base-change` (Stacks 05DC). I checked its statement and source: its hypotheses are locally finite type and quasi-coherent, both established in step 1. Its generic-point condition is exactly the residual condition established in step 5. Pullback composition is in the module pullback definition, and associativity of the scheme fibre products follows from the stated universal property. No part of the proof of another node is used as an unstated conclusion.

Step 7 proves the closure-disjointness assertion directly by continuity: a point in the forbidden intersection would map to the forbidden intersection downstairs. The cited purity definition contains all other impurity clauses. The contradiction therefore proves precisely the item's assertion, with no additional hypothesis and no weakened conclusion.

For the B–E audit, all objects are introduced, the statement and dependency IDs were opened and read, quotations are verbatim, the proof dependencies are the union of uses, and no statement-only node restates the item. I tested the empty source and zero module (there is no impurity), identity base change (the construction returns the same obstruction), and a field extension with non-isomorphic residue fields (the retraction at the new elementary neighbourhood still applies). The local-spectrum lifting also works when t'=t by choosing the closed point. No new statement or source correction is required.
