# Q44 stage-1 delivery: lem-trf-coefficient-field-generator-presentation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coefficient-field-generator-presentation.json`: existing statement node, now split into four steps; full-item Mathlib searches find no match.
- `citations.json`: nine step/node entries, each copying the cited node's statement verbatim.
- `report.md`: this report. `searches.jsonl` is the unedited search-command log.

No new nodes and no new Mathlib leaves. The existing statement, source, statement dependencies, creation record and blueprint ancestry are retained.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag, identifier variants, prescribed coefficient data, and related power-series presentations found no declaration covering every clause. In particular `IsLocalRing.cohen_structure_power_series_surjection` in `RingTheory/CohenStructurePowerSeriesSurjection.lean` chooses its coefficient ring and number of parameters existentially. Its internal presentation argument is not a public declaration with the item's signature. `MvPowerSeries.exists_ringHom_of_isAdicComplete` is the existing evaluation tool, not a proof of surjectivity and finite kernel for this item.

## WANTED

None. All mathematical sources needed here are available locally.

## Findings and corrections

The item was statement-only, and there was no earlier sandbox node or report to resume. The statement is correct and needs no dispute or correction. Varieties 0C52 supplies the intended route after the coefficient section has been fixed. Algebra 0315 supplies the completion surjectivity argument. The source's terse phrase that both sides are complete becomes a precise application of the existing complete-source lemma after checking that the extended variables ideal is the target maximal ideal. This avoids treating the target as a finite module, which is neither assumed nor needed.

The residue-preimage assertion is proved explicitly, rather than inferred from surjectivity alone. Kernel finite generation uses Noetherianity of the source power-series ring, not merely Noetherianity of the target. No new lemma duplicates a clause of the item: all non-elementary tools already exist in the DAG.

## Unfinished work

None in the requested one-level split. Existing cited nodes retain their own stage statuses; this delivery does not claim to finish their formal proofs.

## Searches and blueprint route

Read the chapter record `sec-trace-formula`, unit `sk-i-curve-zero`, the current main-20261015 local-term-locality proof, and the item's recorded chain to that blueprint ancestor. This item remains an algebraic formal-presentation ingredient below that chain; it does not replace the unit's contracting-correspondence argument. `tools/blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality`. The whole-blueprint search `power series` finds fifteen blueprint nodes, none stating this prescribed-section presentation. Whole-DAG searches by 0C52, 0315, power-series evaluation, completeness and Noetherianity identify the existing generic nodes used below. The item's `same_as` remains empty.

Ran all four required search commands and a second natural-language phrasing through msearch.py, read their hits, and recorded their exact queries and logged results. The completeness hit is a source-completeness theorem; constants surjectivity assumes an empty variable type; completion evaluation maps land in quotients of the same ring; polynomial algebra generators and finite-presentation coefficient data concern polynomials; coefficientwise PowerSeries.map_surjective requires an already surjective coefficient map. None states the entire item. Historical Q22 search records were preserved as provenance; the current Q44 records are additionally present and match searches.jsonl.

## Not duplicates

No new nodes. Existing generic results are reused without changing their files.

## Review by Q44

I read Varieties Tag 0C52 (`lemma-complete-local-ring-structure-as-algebra`), especially its last paragraph with the coefficient field chosen before the maximal-ideal generators. I also read Algebra Tag 0315 (`lemma-completion-generalities`) and its successive-approximation proof, the complete-ring definition 0317, the final presentation paragraph of 032A and field power-series assertion of 032C, the proof of 0306 (`lemma-Noetherian-power-series`), and the opening definition in 00FM. The field is already a coefficient field by hypothesis, so no Cohen-ring existence or separable residue-field lifting is required. There are no new nodes requiring separate source verification.

For step 1 I opened `lem-weil-pbc-power-series-universal-property-complete` and checked its actual statement: its coefficient ring and target are arbitrary commutative rings, its target is complete for the specified ideal, and its parameter family lies in that ideal. Taking the item's prescribed sigma and y therefore gives exactly the map and values used. Agreement on constants is exactly the algebra-homomorphism condition. Mapping the variables ideal produces the ideal generated by the y_i, hence exactly n. The image of its rth power is in n^r, which is the elementary continuity check at zero and, by translation, everywhere.

For step 2 the same evaluation statement explicitly includes congruence to every finite truncation; at degree one the truncation is the constant term. The section identity gives rho pi Phi(g) = a_0. I opened `lem-weil-pbc-power-series-combined-ideal-coefficients`: its coefficient criterion holds over any commutative base and for any base ideal, so with J=0 and exponent 1 the only tested coefficient is the constant coefficient and its required ideal is 0. This is exactly membership in I. Injectivity of rho makes this equivalent to membership of Phi(g) in n. I did not use an unstated assertion that the variables ideal is maximal.

For step 3 I opened both cited definition nodes: Noetherian means every ideal is finitely generated, so the two ideals of a field suffice; completeness means bijectivity of the quotient-tower map and includes separatedness. The zero-ideal tower has constant positive part, proving the base-completeness hypothesis. I opened `lem-weil-pbc-power-series-complete-over-complete-base`; it takes a Noetherian base complete for J and concludes completeness for J A plus the variables, exactly I for J=0. I opened `lem-weil-pbc-complete-source-surjective-mod-ideal`; it only needs precompleteness of the source, Hausdorffness of the target for the extended ideal, and surjectivity of the quotient composite. All three have now been verified, and the quotient lift is the constant rho(b), since pi sigma is rho inverse. I read the corresponding Mathlib signature in AdicCompletion/Functoriality.lean:447 to check this interpretation. These are generic algebra tools from another unit, so their individual reasons are declared in split_report.tool_uses.

For step 4 I opened the statement of `lem-weil-pbc-power-series-noetherian`: it accepts any Noetherian commutative coefficient ring and any finite number of variables, including zero. It makes the source Noetherian. The cited Noetherian definition then supplies finite generation of its kernel as an ideal. Generators are chosen inside that kernel, and step 2 places them in I. No regularity, minimality of y, injectivity of sigma as an extra hypothesis, or finite-dimensionality of R over F is used.

I checked edge cases: n=0 forces n=(0), so rho and the section identify R with F; the presentation is sigma and its kernel has the empty tuple. With nonempty redundant generators or some y_i=0, the ideal-image calculation and all four steps remain valid. For R=F and arbitrary n with all y_i=0 the map is constant coefficient and the kernel is I; for R=F[e]/(e^2) with y=e the kernel is (T^2); for R=F[[u]] with y=u the kernel is zero. The zero ring is excluded automatically by the field residue isomorphism. The kernel tuple is allowed to be empty without forcing n=0.

Against delivery-errors B--E: all objects and topology ideals are explicit, TeX uses ordinary single mathematical escapes after JSON decoding, no new statement or proof node is introduced, and every non-elementary step names an existing statement with the required hypotheses. The nine verbatim citations make those checks inspectable. The proof contains no unstated transport, no hidden choice of a different coefficient field, no new cycle-producing dependency on a descendant, and no step exceeds 2000 characters (lengths 602, 461, 798, 528). The existing generic tools are strictly below this assembly and do not restate its conclusion.
