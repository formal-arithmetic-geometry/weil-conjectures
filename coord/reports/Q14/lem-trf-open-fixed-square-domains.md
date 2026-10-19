# Q14 stage-1 report: lem-trf-open-fixed-square-domains

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-open-fixed-square-domains.json`: statement, six proof steps, no new nodes; Mathlib searches found component facts, with no complete match. The item's mathematical statement is unchanged.
- `citations.json`: 35 step/node entries with verbatim statement quotations.
- `report.md`: this report, retaining the earlier attempt's findings and recording the recovery audit.

## Attachments

None. The retained search and the recovery search of slopmaster2 found no occurrence of the item tag and no project declaration giving all its clauses. I read the fixed-square declarations in `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean`, including `isPullback_fixι_toProd`, `isClosedImmersion_fixι`, and `isGeometric_fixStr`: these cover portions of the fixed-scheme geometry, not the assertion for arbitrary geometric `c` and an arbitrary open restriction. No attachment is claimed.

## WANTED

None.

## What I checked and corrected

The sandbox already held the earlier six-step split, report, quotations, and logged searches. I ran the required dry run before changing them; it exited with preflight passed at cd3393bc46. I compared the item with the current unsplit repository version and kept the statement and statement dependencies. I restored its original `created.item = lem-trf-trace-class-open-restriction` and original group/date rather than treating an existing node as newly created by itself. All authoritative inherited Mathlib searches and all seven sandbox-logged searches are retained; successful searches only found components, and the inherited rate-limited LeanSearch remains `unavailable`. No searches were invented or repeated.

I checked the current blueprint's `lem-trf-local-term-locality`, its current DAG proof, the unit `sk-i-curve-zero`, and chapter `sec-trace-formula`. The first paragraph localizes the support to an open neighborhood; this auxiliary item supplies the geometric domains for that restriction. The nearest blueprint ancestor remains `lem-trf-local-term-locality` through `lem-trf-trace-class-open-restriction`. Whole-blueprint searches for fixed-square and separated finite-type assertions found related Cartesian-square and base-change nodes, but none with this exact collection of geometric assertions. No unit or chapter route is changed.

The previous finite-affine-chart step contained a wrong diagonal identification: the diagonal of `c:C→Z` was said to be a base change of the diagonal of `Z`. I replaced that argument with the graph square. Its functor-of-points equation is written explicitly: the second coordinate must equal `c` of the first, with inverse given by the first projection. Thus the graph is a closed base change of the closed diagonal of `Z`, and `c` factors through that closed graph and the base change of `C→s`. This is a few-line argument from the existing pullback and permanence statements, not a new graph node. The item itself is true, so no statement dispute arises.

I also corrected the open-immersion verification: quasi-compactness of `W` alone does not prove quasi-compactness of `j`; the proof now checks `j⁻¹(V)` for every affine open `V` in the Noetherian target `C`. The existing `lem-weil-pbc-separated-cancellation` supplies separatedness of the open immersion. The properties of `j'` now follow directly by base change of the already verified `j`. Step 3 explicitly records separatedness and finite type of `i`, and Step 5 explicitly cites both composition lemmas for the structure map of `F_W`. The auxiliary scheme proof is marked agent-written: Varshavsky states the convention and the fixed square but does not spell out these scheme permanence arguments.

## Review by Q14

I read Varshavsky §0.2 (all schemes separated finite type), §1.1.9 (restriction to an open support), and §1.2.1 (the Cartesian fixed square). For the scheme arguments I read the local Stacks source: Schemes Tags 01KS (`lemma-semi-diagonal`), 01KU (`lemma-separated-permanence`), 01L7 (`lemma-immersions-monomorphisms`) and 01JY (`lemma-base-change-immersion`); Morphisms Tags 01T3, 01T4, 01T6, 01QR and 01W5; and Properties 01OV, 01OW and 01OZ. There are no new nodes needing independent sources or searches.

For Step 1 I opened the statements of `lem-weil-pbc-finite-type-over-noetherian`, `lem-pod-separated-finite-type-base-change`, `lem-sfb-finite-type-composition-base-change`, and `lem-weil-pbc-proper-fp-permanence`. They respectively give Noetherianity, the properties of both product projections, finite-type composition and separated composition. The field base is Noetherian by the explicit one-point/field-ideal check.

For Step 2 the universal property in `def-pc-fibre-product` gives exactly the graph-square identification written in the step. `def-weil-proper-morphism` defines separatedness by a closed diagonal; the closed-immersion-base-change node applies to the diagonal of the already separated `Z`; the closed-immersion-proper node gives the graph's separatedness and finite type. The projection to `Z` is a base change of the hypothesized separated finite-type `C→s`. The same two composition statements then give all properties of `c`. Each non-elementary inference is one of those cited statements; the graph identification itself is elementary and written out.

For Step 3 `def-trf-fixed-scheme` explicitly gives `F=C×_Z X` with precisely the two projections used. The closed-immersion-base-change statement applies to `i`, and separated-finite-type-base-change applies to `d`, with no hypothesis on the base-changing map. Closed immersions are proper, so both `Δ` and `i` are separated finite type. The composition statements apply to the structure morphism of `F`.

For Step 4 the Noetherian-open node states that every open subscheme of a Noetherian scheme is Noetherian and quasi-compact. Applying it to each inverse image of an affine target open proves the hypothesis of the quasi-compact-open-immersion finite-type node. Clause (a) of separated-cancellation explicitly includes open immersions. Both composition nodes then give `W→s` and `cj`.

For Step 5 I verified the projection orientations: `i_W` is the base change of the closed `i`, while `j'` is the base change of the open `j`. The closed/open immersion base-change statements say exactly this. Closed-immersion-proper and the two composition nodes give the structure map of `F_W`; separated-finite-type base change gives all claimed morphism properties of `j'`. Step 6 uses only the two composition statements to verify `dj'` and assemble the maps already checked.

I opened every cited node and checked its statement, not its proof; the 35 quotations in `citations.json` are verbatim portions of those statements. All non-elementary cited results are existing Mathlib leaves; definitions are used for their stated constructions. No off-route theorem or SGA source is used. I checked empty `W`, `W=C`, empty `C`, nonreduced schemes, and nonproper affine `C`: pullback and permanence arguments work in each case without introducing reducedness or properness. No proof step exceeds 2000 characters, no clause is moved into a helper, and no new node, duplicate or cycle is introduced.

## Unfinished work

None in the stage-1 split. The maintainer's independent review remains the delivery workflow's next review.
