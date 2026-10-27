## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-finite-fan-chart-cech-cover.json`: item, statement unchanged, status split, eight proof steps; logarithmic assertion absent from Mathlib.
- `citations.json`: one entry for every use in every step, with the verbatim statement of the cited node.
- `report.md`: this report. `searches.jsonl` was written by the required msearch command.

## New nodes

None. There are zero new Mathlib leaves. In particular I did not introduce separate nodes for finite disjoint-union fan charts, chart transport by a strict morphism, the Cech induction, or a clause of this item. These are explicit assembly steps from the existing statements and definitions.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact blueprint tag, the item id, `fan.?chart`, `LogScheme`, `LogStructure`, and `KatoFan` found no project declaration covering the item. Ordinary etale declarations do not assert anything about logarithmic structures or characteristic fans. No sorry declaration is claimed as finished.

## Wanted

None. The ILO PDF and the Stacks TeX sources needed here are present.

## Findings and changes

The imported node had no proof. Its finite-neighborhood existence clause is already explicitly stated in `lem-trf-log-fan-chart-blowup` (i), so no new existence lemma is warranted. The remainder requires construction of the disjoint union and a verification of scheme quasi-compactness, not just a bare appeal to etale base change. The proof now supplies these, an fs product comparison, characteristic-chart transport and the induction on the number of factors. No statement or original source field was changed. All inherited searches and blueprint provenance were retained.

The current `literature/blueprint/latest` points to `main-20261023-1620`, commit 7284bb09daf97437d544c51882b325f9c52cd345. I read its chapter, unit and ancestor proof. The current zero-stalk unit uses contracting correspondences, while this item's inherited provenance explicitly identifies a historical nearby-duality/alteration branch. I preserve that provenance rather than claiming the current ancestor proof still contains a log-resolution argument. This split only resolves the already-assigned log-cover lemma; it changes no chapter or unit route and no unit realization fields.

## Searches

Whole-DAG searches by ids, title and statement keywords found the fan-chart existence, scheme coproduct, finite coproduct etaleness, quasi-separatedness, quasi-compact permanence, etale covering base change, finite-type Noetherianity, strict-log characteristic comparison and fs-product comparison nodes used here. I opened their statements before using them. Blueprint searches `fan chart`, `fan`, `strict morphism`, `finite coproduct`, and `01T6` were run; no blueprint node states this entire logarithmic Cech-cover assertion. The ordinary finite-type Noetherian lemma is reused rather than recreated.

The item's msearch log records five new actual calls: two LeanFinder phrasings (one for strict log fibre products, one for finite fan-chart covers), LeanSearch for disjoint-union logarithmic fan charts and pullbacks, Loogle for `"LogScheme", "Etale"`, and grep for `LogStructure|LogScheme|KatoFan|fan.?chart`. All returned successfully. Loogle and grep returned zero hits. The semantic searches returned ordinary scheme pullbacks, finite morphisms, quasi-compact covers, extensive categories and manifold charts. I read the returned types and the source `Mathlib/AlgebraicGeometry/Cover/QuasiCompact.lean` (definition at line 38, open-cover instance at 79, base-change instance at 95), and `Mathlib/AlgebraicGeometry/Limits.lean` (finite extensivity at 456). These do not contain fs log structures or fan charts and do not specialize to this item in one line. The searches in the node exactly reproduce the command's query strings and returned records; old searches remain historical.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish.

## Tool uses

`lem-sc-etale-coproduct-etale` supplies an ordinary finite-coproduct etaleness fact; its statement is about arbitrary scheme etale morphisms, unlike `lem-exc-etale-coproduct-etale`, which is only about spectra of finite separable field extensions and would not suffice here. `lem-per-fs-product-finite-comparison` supplies fs-product existence and the strict case of the underlying-scheme comparison; its local-Noetherianity hypothesis is proved before invocation. Both are generic tools, declared in `split_report.tool_uses`, not an alternate proof route. The quasi-compact permanence, Noetherianity and covering base-change lemmas are existing Mathlib leaves.

## Review by NK

I read ILO Expose VIII 3.3.4(ii), 3.3.5--3.3.6, 3.3.8, 3.3.12--3.3.13 and the proof of 3.3.15 on printed pp.107--110 (PDF pp.113--116); the last proof actually forms finite disjoint unions of chart neighborhoods. The present item makes the Cech and common-refinement geometry implicit in that descent reduction explicit. For ordinary scheme facts I read Stacks `properties.tex`, label `lemma-locally-Noetherian-quasi-separated` (01OY), `schemes.tex`, `lemma-quasi-compact-permanence` (03GI), and `morphisms.tex`, labels `lemma-finite-type-noetherian` (01T6), `lemma-etale-characterize` (02GJ), `lemma-composition-etale` (02GN), `lemma-base-change-etale` (02GO), and `lemma-base-change-surjective` (01S1). There are no new-node statements requiring a separate source check.

Step 1 uses the finite-cover clause of `lem-trf-log-fan-chart-blowup` itself, not its proof. `lem-weil-pbc-locally-noetherian-quasi-separated` explicitly gives quasi-separatedness. Clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` explicitly allows any morphism from a quasi-compact source to a quasi-separated target. The definitions `def-weil-etale-morphism` and `def-weil-unramified-morphism` supply locally finite type for the etale maps. The source and target are quasi-compact, so the maps are finite type and the statement of `lem-weil-pbc-finite-type-over-noetherian` applies to the Noetherian scheme X. This avoids invoking the locally finite type version from a node that states only the finite type version.

Step 2 uses the full disjoint-open-components conclusion of `lem-weil-pbc-scheme-coproduct-family`. `def-trf-fs-log-blowup` supplies the sheaf and units condition and the fs local-chart predicate; `pqf-def-locnoeth` supplies the affine-cover definition. `def-per-strict-log-morphism` explicitly identifies the actual characteristic maps at geometric points, giving torsion-freeness from X. Product sections on disjoint etale pieces satisfy gluing componentwise. Combining finitely many finite subcovers is the written elementary quasi-compactness argument; it does not assume an infinite coproduct is quasi-compact.

Step 3 uses the locally affine definition of a fine fan in `def-trf-fine-fan-blowup` and the fan-chart definition in `lem-trf-log-fan-chart-blowup`. The componentwise construction is on disjoint opens, so no gluing comparison on a nontrivial overlap is suppressed. `lem-sc-etale-coproduct-etale` states precisely the etaleness of a finite coproduct of arbitrary etale scheme maps; strictness is verified pointwise using the characteristic equivalence of `def-per-strict-log-morphism`. The family is finite, as required by the coproduct-etale lemma.

Step 4 uses the ordinary fibre product of `def-pc-fibre-product`. `lem-weil-pbc-etale-covering-base-change` applied to the singleton {U -> X} gives surjectivity and etaleness of W -> Y for ANY Y -> X. `lem-weil-pbc-etale-scheme-base-change` gives etaleness of the other projection without surjectivity. The quasi-compact permanence node states all three implications actually used: quasi-compact U and quasi-separated X imply quasi-compact u; base change preserves quasi-compactness; quasi-compact morphism and quasi-compact target imply quasi-compact source. The finite-type Noetherian lemma then applies to p with Noetherian target Y after the two cited etale/unramified definitions give locally finite type. No properness, separatedness of X, or surjectivity of f is used.

Step 5 invokes the STATEMENT of `lem-per-fs-product-finite-comparison`, which grants the fs product and says the comparison with the ordinary product is an isomorphism when either input is strict. Its local-Noetherianity hypothesis on the ordinary product was checked in step 4. The local strict chart calculation is written as the monoid pushout P amalgamated with P over P, hence P, with identity maps. This verifies strictness of BOTH projections using the characteristic criterion of `def-per-strict-log-morphism`, rather than inferring it from the scheme comparison alone. The chart predicate and group-completion notion are those of `def-trf-fs-log-blowup`. No claim about arbitrary nonsaturated products or arbitrary nonstrict maps is needed.

Step 6 uses only the FIRST assertion of `lem-trf-strict-log-blowup-cartesian`: for a strict map with Zariski target log structure, its source log structure is Zariski and the canonical inverse-image characteristic map is an isomorphism. Its statement explicitly contains that assertion independently of all later ideals and blowups, which are not invoked. The remaining argument is the displayed composition of inverse-image sheaf isomorphisms and the definition of fan chart in `lem-trf-log-fan-chart-blowup`. In particular I do not cite the latter's blowup-tower compatibility clause as if it alone stated arbitrary characteristic transport.

Step 7 is the induction on r, with base r = 1 and step adjoining one factor. It uses the previously proved steps, the projection-compatible uniqueness in `def-pc-fibre-product`, strictness as pullback of log structures in `def-per-strict-log-morphism`, and the explicit etale composition clause (2) of `lem-weil-pbc-etale-composition-cancellation`. Permuting factors identifies every omitted-factor projection with the base-change projection, so the claim is not confined to the last projection. Surjectivity is preserved under composition directly on points.

Step 8 applies steps 4--6 with Y = V and uses the singleton covering-base-change lemma for the OTHER projection. This explains why both projections are surjective in the common-refinement clause whereas only the projection to Y is asserted surjective in the final arbitrary-f clause. The fibre product and empty fan have the meanings of `def-pc-fibre-product` and `def-trf-fine-fan-blowup`; their universal and pointwise predicates give the explicit empty-case argument.

I tested X empty with the empty family, the identity cover, trivial characteristic monoids (the zero monoid and the one-point fan), repeated factors in the Cech nerve, and a nonsurjective open Y -> X with nonempty complement. The latter shows why the proof must not claim W -> U surjective in the last clause. Quasi-compactness uses local Noetherianity of X only through the cited quasi-separatedness lemma, so it is not the false assertion that fibre products of arbitrary quasi-compact schemes over an arbitrary base are quasi-compact. No source or item statement correction was necessary. I corrected the potential citation mistakes above by using the arbitrary-scheme coproduct-etale node and proving finite type before applying the Noetherianity node. All eight steps are under 800 characters; none passes the 2000-character long-step threshold. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these statements and sources: no statement-only node hides a proof, no duplicate is introduced, and the cited node graph contains no path back to this item.

## Unfinished

No mathematical clause is left unresolved. Required server validation and direct delivery follow this report; their results are recorded below when available.
