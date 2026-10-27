# Worker report: lem-per-log-smooth-trait-punctual-purity

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-trait-punctual-purity.json`: existing statement split into three assembly steps, using three existing admitted inputs. No new nodes; no Mathlib leaves.
- `citations.json`: one literal statement quotation for each of the three step/node citations. Each quotation was checked against the current input JSON.
- `repair-admitted-inputs-audit.json`: base digest, preserved fields, completed initial dry-run diagnostics, input/quotation checks and step lengths.

The earlier report is retained verbatim as `report-retained-pre-admission.md` in the sandbox, alongside all previous audit files, citation evidence and `searches.jsonl`. Its BLOCKED dispositions describe the admission boundary before the maintenance extension and are superseded by this report. The source assembly and five actual searches from that report are retained here and in the item; no completed search was repeated.

## Attachments

None. A fresh exact-tag and concept search of `lean/WeilConjectures/` found no declaration for this item. The broader punctual-purity hits are Frobenius-weight statements about Weil sheaves, a different notion. The input nodes' withdrawn theorem attachments are not evidence of completed proofs.

## WANTED

None. The ILO volume is available locally, as is the current blueprint under `literature/blueprint/latest/`.

## What was wrong and what changed

The retained sandbox was identical to the current live item before repair: its statement was intact but it had no active proof. Its report had the correct source assembly but could not activate the three excluded prerequisites. The maintenance decision `coord/changes/20261024-N0-log-smooth-purity-inputs.md` now admits exactly `lem-per-regular-log-smooth-monomial-chart`, `lem-per-monomial-trait-punctual-purity` and `lem-per-punctual-purity-etale-locality` as UNSPLIT work with their former proofs withdrawn. The current released repair note explicitly authorizes citing those statements. All three current records have empty proof and proof_deps, so citing their interfaces does not restore their old proof graphs.

I preserved the item's statement, source, stmt_deps and complete blueprint record verbatim, together with its creation, chapter, unit and audit records. I supplied the three-step source assembly, proof_deps equal to the union of step uses, documentary proof_origin and split_report. The original Mathlib searches remain; the five real retained queries were additionally recorded with their exact logged tool/query/date and returned names. No definition, theorem statement, child node, Lean module or maintenance-owned field was changed.

There is no statement dispute: the item is the finite-coefficient specialization of ILO, Expose XVI, Theorem 3.6.2, printed p.252. Its ordinary small-etale coefficient category, Kummer class and dimension normalization are the same as those in the monomial-purity and locality inputs. The source's final sentence on printed p.253 deduces this theorem from Propositions 3.6.5 and 3.5.12. The locality step makes the implicit etale-local passage explicit.

## Source assembly

1. For arbitrary v in V, choose a uniformizer pi of R and apply `lem-per-regular-log-smooth-monomial-chart`. It gives regular affine Noetherian U, etale a:U -> V, u above v and an etale S-map b:U -> T, with T defined by product T_i^{e_i}=pi and nonnegative, not-all-zero exponents. This is ILO XVI 3.6.5, p.253, using 3.6.3, p.252.
2. Apply `lem-per-monomial-trait-punctual-purity` to this same R, pi and tuple. The result makes T regular Noetherian and punctually pure, hence pure at b(u). This is ILO XVI 3.5.11--3.5.12, p.250, as used at the end of p.253.
3. Apply `lem-per-punctual-purity-etale-locality` first to b at u to obtain purity of U at u, then to a at u to obtain purity of V at v. The source and target schemes are regular Noetherian before each application; ell remains a unit by its image from R. Arbitrary v gives the conclusion. This exposes the pointwise locality from ILO XVI 3.2.1--3.2.2, p.244, in the concluding argument on p.253.

## Mathlib searches

These are the five actual commands retained in `searches.jsonl`, all run through the required `msearch.py N0 lem-per-log-smooth-trait-punctual-purity` wrapper on 2026-10-24. I read the returned names and retained result assessments. The statement and the search questions have not changed.

- leanfinder: `Regular fine saturated log smooth schemes over a discrete valuation ring are punctually pure in etale cohomology with finite coefficients`. Eight hits concern Scheme.Etale, IsEtale-to-IsSmooth, formal unramifiedness, standard smooth relative dimension zero, etale loci and smooth charts. None gives the Kummer-supported purity isomorphism.
- loogle: `"LogScheme"`. Zero hits.
- grep: `LogScheme|LogSmooth|log.smooth|punctual.*pur`. Zero hits.
- leansearch: `Etale cohomology with support at a point of a regular log smooth scheme over a trait is a Tate twist`. Eight hits concern IsEtaleAt, etale neighborhoods, the small etale topology, etale morphisms and localization. None states the item.
- leanfinder, second phrasing: `The extraordinary inverse image of the constant finite etale sheaf along a closed point of a regular logarithmically smooth scheme over a trait is the shifted Tate twist`. Eight hits concern structure-sheaf stalks, etale loci, standard-etale algebra maps and normalization diagrams. None states the extraordinary-inverse-image or fundamental-class assertion.

No service was unavailable. The original historical search records in the item are preserved as inherited data; no new search was invented. No Mathlib leaf is claimed.

## Blueprint and duplicate search

I read the chapter and unit records, the three levels of SETUP, and the latest blueprint ancestor `lem-per-artin-gabber-affine-curve` with its proof. `blueprint_refs.py ancestor` confirms that ancestor. Its Step 3 and the retained via chain are historical provenance for the regular finite-torsion input, not a proof of the discarded arbitrary-field adic-duality argument. The current delivery uses only the newly admitted ILO finite-coefficient interfaces, leaving the ancestor, chapter and unit unchanged.

Whole-DAG searches by source numbers 3.6.2, 3.6.5 and 3.5.12 and by log-smooth/monomial-trait concepts locate the three existing inputs. Whole-blueprint searches for `log smooth`, `monomial` and `cohomological purity` find respectively zero, eight and two records. The monomial hits concern projective/affine coordinates or coherent cohomology; the purity hits are the affine-line orientation/purity results in their fixed conventions. None duplicates the arbitrary-trait statement. The three needed input records already exist, so I created no aliases. All three share the item's unit; no off-unit tool approval is needed.

## Not duplicates

No new nodes were created. The three input ids are cited unchanged rather than recreated under new names.

## Review by N0

I independently read ILO XVI printed p.244 (Definitions 3.2.1--3.2.2 and strict-henselization invariance), pp.250--251 (Definition 3.5.11, Proposition 3.5.12 and Lemma 3.5.13), and pp.252--253 (canonical trait log structure, Theorem 3.6.2 and Propositions 3.6.3--3.6.5). I opened the full current statements of all three cited nodes. I did not rely on their titles, prior reviews or withdrawn proofs. The source explicitly assembles the theorem from the chart and model result; the supplied locality interface expresses the pointwise passage used there. No new node requires a separate source review.

Step 1 takes both etale maps, regular affine Noetherian U and a point over the prescribed v from the chart's statement. That statement assumes exactly an fs log-smooth morphism to the canonically logged trait and a regular Noetherian source, all supplied by the item. It provides an etale model map, not just an unspecified smooth chart. Step 2 uses the monomial statement's explicit regularity AND punctual purity conclusion for exactly the same equation and exponents. Its arbitrary-trait hypotheses and ell-invertibility are already in force. Step 3 uses the locality statement's pointwise iff in opposite directions along b and a, at the actual image points t=b(u) and v=a(u). It requires regular Noetherian schemes, so I check U from step 1, T from step 2 and V from the item before either application. The image of an inverse for ell in R is an inverse in each structure ring, which is the elementary coefficient check. The citations use statements, never properties buried in their proofs (C3/C4).

For C1/C2, the three non-elementary ingredients are individually cited and every step is marked non-elementary. Choosing a uniformizer from the trait definition, instantiating the already supplied tuple, evaluating purity at a point, the unit calculation and universal quantification add no hidden lemma. Each step is below 2000 characters (430, 311 and 578); the entire assembly is 1319 characters. There is no hidden chart calculation, purity proof or comparison identification inline. The coefficient and Kummer-map conventions are literally shared, so no category change or new comparison is being assumed.

I checked E1--E6 against the hypotheses at the applications. Empty V gives a vacuous assertion. Generic-fibre points are not excluded: the chart is stated at every point. For n=1 and exponent one, T is the trait itself, which agrees with the model statement. Tuples with a zero exponent, and exponents divisible by ell or by the residue characteristic, are explicitly allowed by that input; the proof adds no prime-to-ell, completeness, henselianity or excellence condition. No n=0 or all-zero tuple is used. No image subscheme is substituted for a scheme or point, and no codimension is identified across maps by an unsupported assertion: the locality theorem already compares the normalized Kummer maps. These checks reveal no source error requiring a statement correction (E7).

For B1--B10 and C5, there are no new statement-only nodes or leaves to misstate, duplicate or falsely attach; the item introduces its objects and its definition dependencies remain unchanged. The ILO source is named by document and exact proposition, rather than an unrelated Stacks tag. The Mathlib queries and results come from the retained real log, including the second phrasing. Blueprint provenance is unchanged and the split_report explains which source assembly it realizes. For C6--C8 and D1--D5, this is a genuine chart/model/locality assembly of distinct existing statements, with no parent theorem citation, circular induction, replacement by an alias or off-unit route. The admitted children remain independent stage-1 tasks as the repair order requires.

The return's sole substantive issue was the Q84 admission conflict. I checked the new maintenance decision and released repair note against the exact three ids and their current empty proof records. This repairs that issue by using the now-admitted interfaces, while leaving every other exclusion in force. The initial required dry run of the retained artifact completed with exit 1 and six accurate unfinished-split diagnostics: unchanged item, unsplit status, missing split_report, missing proof_origin, missing blueprint realization and an empty-proof review failure. The substantive assembly and its metadata now repair each diagnostic. This review signs the split for the maintainer's independent mathematical review; it does not claim that the three unsplit inputs have already been proved.

## What could not be finished, and why

Nothing remains in this item's one-level stage-1 split. Its three admitted inputs remain UNSPLIT for their own later workers, as explicitly ordered. No Lean was written, no compiler/Lake/build tool or local DAG/preflight checker was run, and no repository or launcher file was edited. Only sandbox files were written. Delivery invocations are kept sequential; the final server dry run and push results are recorded below when complete.
