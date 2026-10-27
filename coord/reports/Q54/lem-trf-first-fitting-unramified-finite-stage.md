# Stage-1 report: lem-trf-first-fitting-unramified-finite-stage

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-first-fitting-unramified-finite-stage.json` (statement, split, no Mathlib match), `citations.json`, and this report. `searches.jsonl` contains the actual searches. No new nodes or Mathlib leaves were created.
2. Attachments: none. The live `lean/WeilConjectures/` search for the exact blueprint tag, first-Fitting names, Fitting, and unramified limit descent found no declaration stating the item. The FpqcDescentEtale source concerns a different descent problem.
3. WANTED: none.
4. Problems corrected: the imported item had no proof. Its statement is retained exactly. The proof now verifies all finiteness hypotheses of Tag 0C4W rather than treating unramifiedness descent as unconditional. The existing first-Fitting definition is not used as evidence for base-change compatibility; that theorem is supplied by the differential and Fitting-pullback nodes. No STATEMENT-DISPUTED issue was found.
5. Unfinished mathematics: none at this one-level split. Existing unsplit dependencies remain their own items.

## Sources and route

Read the chapter and unit records, the three fixed/free blueprint levels of SETUP.md, GOAL.md, the worker and stage-1 rules, and both copies of delivery-errors B--E. Read Stacks `curves.tex`, Tag 0C5F (lemma-descend-nodal-family), especially its last paragraph; `divisors.tex`, Tags 0C3D (lemma-base-change-fitting-ideal) and 0C3I (lemma-base-change-and-fitting-ideal-omega); `morphisms.tex`, Tags 01V0 and 01V2 (differential base change and finite-type differentials), 01T3--01T6 (finite-type composition, base change, immersions, Noetherianity); `properties.tex`, Tag 01OY (locally Noetherian implies quasi-separated); and `limits.tex`, Tag 0C4W (lemma-descend-unramified). These sources give the formation/descent route already named in the item. No SGA source is used.

This is an inherited auxiliary node on the historical nodal approximation branch. Read the current main-20261015 ancestor text, and the live ancestor statement/proof. Neither states this Fitting lemma; its blueprint provenance is historical, not a claim that the current contracting local-term proof itself mentions Fitting ideals. Retained the inherited ancestor/via chain and described this explicitly in split_report. No chapter, unit, or other node changed.

## Searches and reuse

Searched the whole DAG for 0C3I, 0C4W, Fitting, fitting-ideal and descend-unramified, and the blueprint index for Fitting, first Fitting and unramified; ran the ancestor lookup. Reused `lem-trf-relative-differential-sheaf-base-change`, `lem-trf-fitting-ideal-sheaf-pullback`, and `lem-trf-unramified-limit-descent`. The nodal-family-fitting-singular node would require flatness and nodal fibres and is deliberately not applied to the arbitrary morphism here. Its general differential/Fitting dependencies have precisely the needed hypotheses.

Ran both semantic phrasings through msearch, along with LeanSearch, source grep, and Loogle. The first Loogle query rejected Algebra.TensorProduct; the follow-up valid KaehlerDifferential query returns the differential type, its finite-generation result and related declarations. LeanSearch returns unramified base-change and finite-presentation base-change statements; LeanFinder returns unramified-locus, formally-unramified and differential results. None states the Fitting ideal closed-subscheme assertion plus inverse-limit descent. The grep hits are Fitting decompositions of Lie or Artinian modules, unrelated to Fitting ideals. Existing search records in the item are retained as history, and the searches performed here are appended exactly as logged.

## Not duplicates

No new nodes. Existing general lemmas supply the construction, finiteness and limit descent; no clause of the item was repackaged as a new node.

## Review by Q54

I checked the split against B--E with the cited node statements and Stacks passages open. All proof citations have literal statement excerpts (the full statement where that gives the clearest context) in citations.json. None relies on the proof of a cited node or on its source tag alone.

Step 1 uses the explicit polynomial-quotient meaning of local finite presentation in def-sbc-locally-finite-presentation: its variables generate the algebra, so local finite type follows without another theorem. The item assumes quasi-compactness; hence the finite-type definition applies. The finite-type composition/base-change node explicitly permits an arbitrary base-change morphism. The affine-scheme qcqs node supplies both properties of every base. These finiteness results are existing Mathlib leaves, so using them as tools does not replace a unit route.

Step 2 uses exactly the relative-differential-base-change node's canonical isomorphism and its last finite-type assertion. It states quasi-coherence and requires only local finite type for finite generation. Thus the Fitting-pullback theorem's finite-type quasi-coherent hypothesis is justified. It needs no flatness, unlike several neighbouring nodal statements.

Step 3 uses the Fitting-pullback node's actual scheme-theoretic closed-subscheme conclusion, with r=1, together with the definition of Sing. It takes the image ideal, and never asserts that pullback of the ideal injects into the structure sheaf. The fibre-product identification is proved by writing out its universal property, preserving the closed immersion into X_T. T is arbitrary, including nonflat and non-Noetherian bases; S itself is not assumed Noetherian.

Step 4 is elementary from the closed-immersion node's affine quotient description: A/J is generated by the empty set as an A-algebra, and Spec(A/J) is quasi-compact by the affine-scheme node. This proves local finite type and quasi-compactness on each affine target test. It does not assume J finitely generated or the immersion finitely presented. This is why no unnecessary new immersion lemma was created.

Step 5 uses the finite-type composition node for the complete chain Z_i to X_i to S_i to Spec Z, and separately for Z_c to S_c. The Noetherianity node explicitly includes Spec Z and the finite-type-over-Z consequence. Its definition of Noetherian includes quasi-compactness. The locally-Noetherian-quasi-separated node gives precisely quasi-separatedness, which finite type alone over a general non-Noetherian base would not supply. Each invoked node says the claimed clause, with all hypotheses established in preceding steps or in the item.

Step 6 instantiates the descent node with U_0=Z_c and V_0=S_c, not with X_c or a fibre. Both are qcqs and g_0 is locally finite type by the earlier steps. Its base changes are the same closed schemes identified in step 3. The assumed unramifiedness is of Z to S, precisely the resulting limit morphism. I wrote out directed-tail cofinality to explain why starting at c causes no issue. The node explicitly has no flatness, finite-presentation or Noetherian requirement on g_0. The conclusion is a single stage d at or above c, as requested.

Small cases checked: empty X or Z (including g with relative differential rank at most one, for which Fit_1 is the unit ideal); a constant inverse system; an arbitrary nonflat quotient base change; and a base limit that is non-Noetherian. Quotient finiteness works even for non-finitely-generated ideals; all Noetherian arguments concern finite stages only. No false statement or extra hypothesis was introduced. All steps are below 2000 characters; the only elementary step carries the displayed affine-quotient argument. Proof dependencies equal exactly the union of uses. There are no new definitions, hollow data, or inline unsplit proofs to audit.
