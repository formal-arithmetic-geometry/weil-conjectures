# Stage-1 worker report: lem-sfb-trait-nodal-etale-dvr-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-nodal-etale-dvr-model.json`: statement, split into seven steps; no Mathlib match for the whole statement.
- `citations.json`: one verbatim statement quotation for each step/node pair (15 pairs).
- `report.md`: this report. The sandbox also holds the prescribed search log and a local JSON-writing script.

No new nodes, no new Mathlib leaves, no unit changes, and no Lean files or compiler invocations.

## Attachments

None. Searched the whole live `lean/WeilConjectures/` for the blueprint tag and for trait/nodal/chart terminology. The trait-stalk theorem only concerns local rings of etale schemes over a trait; it gives neither a nodal equation nor the smooth-generic refinement, so it is not an attachment.

## WANTED

None for this split. The required sources are in `literature/stacks-project/`. No SGA source is used.

## Findings and changes

The statement is retained exactly. Its arbitrary-DVR and non-quasi-compact scope agrees with 0CDD. The smooth-generic refinement is local and does not inherit the quasi-compactness hypothesis used later in 0CDE for a finite blowup sequence.

An existing node, `lem-sfb-dvr-nodal-etale-local-form`, already states the 0CDD existence theorem, with an unspecified uniformizer of the etale DVR extension. I reused that statement rather than creating another 0CDD node or expanding its internal proof. The present item adds the fixed original uniformizer and the exclusion/replacement of the zero-parameter model when the generic fibre is smooth. The seven steps prove these additions, including the detail explicitly omitted in 0CDE.

The source's unit absorption is implemented by explicit inverse ring maps: if pi'=epsilon*pi, the new coordinate is epsilon^(-n)*a_old. This records the direction of the change unambiguously.

Five fresh searches ran through msearch.py, in addition to preserving the item's inherited search records: grep, Loogle, LeanSearch, and two LeanFinder phrasings. All services answered. Hits were standard etale presentations, standard smooth charts, etale-locus localization and elliptic good reduction. Their returned statements do not give an arbitrary nodal family's singular normal form or the refinement here. Search records retain the actual query and returned log entry. Blueprint search for nodal found no matching blueprint node; ancestor returned None, as in the item's existing provenance. The inherited blueprint place is already specific and is preserved.

## Not duplicates

lem-sfb-trait-nodal-etale-dvr-model vs lem-sfb-dvr-nodal-etale-local-form: the existing node supplies the normal form with any uniformizer pi' of R'; this item proves it with the originally chosen pi and proves the additional smooth-generic conclusion. It cites the existing node and creates no competing normal-form node.

No new-node pairs require comparison. The other 0CDD occurrences (`lem-sfb-common-nodal-model`, `lem-sfb-nodal-trait-regularization`, `lem-sfb-persistent-node-normalization`, `lem-sfb-point-blowup-fibre-defects`) use local charts in larger constructions and do not replace the smaller existing chart theorem.

## Review by O1

I read models.tex 0CDD (lemma-etale-local-at-worst-nodal), including its smooth case and unit absorption, and 0CDE (lemma-blowup-at-worst-nodal), through the paragraph excluding the persistent-node chart. I also read the current blueprint direct-images proof (3), the unit and chapter records, SETUP's three levels, and both copies of delivery-errors B--E. The split stays within the inherited local prerequisite of the alteration/regularization branch. There are no new nodes whose sources need separate verification.

Step 1 uses precisely the statement of the existing 0CDD node. The given condition at every nonsmooth geometric point implies the existing node's closed-point condition, and reducedness, pure dimension, flatness and local finite presentation are all present. Its stated diagram supplies both etale arrows, the chosen point and the etale DVR extension; no proof-internal construction is used.

Step 2 uses the exact maximal-ideal formula of `lem-weil-pbc-etale-prime-generates-maximal`. I checked algebra.tex 00U4 part (1). Locality makes the contracted prime the maximal ideal of R; localization of R' at its own maximal ideal changes no elements. The definition of uniformizer then gives the original pi as generator. There is no appeal to regularity of the completion or excellence.

Step 3 is elementary cancellation and substitution. Both generators are nonzero in the DVR domain. I wrote the inverse coordinate maps and checked their products; n=0 causes no exception. The cited etale composition/cancellation node explicitly includes open immersions and composition, so composition with the spectrum isomorphism preserves the chart. This permanence citation was added during self-review to avoid silently assuming that the changed chart maps remain etale.

Step 4 proves smoothness of the Laurent opens directly from the lifting definition of `def-sbc-smooth-morphisms`: the displayed finite presentation and correction of an inverse across a square-zero ideal give the whole argument. It does not cite a definition as a substitute for an unstated Jacobian theorem. The computation works over any coefficient ring, including mixed characteristic and imperfect residue fields.

Step 5 uses only the stated smoothness of etale maps, the exact smooth-composition theorem, and the pointwise assertion in `lem-trf-etale-source-smoothness`. I read descent.tex 036U and morphisms.tex 01VA. Applied over the same original base S to both chart arrows, these show that a nonsmooth x cannot map into either smooth Laurent open or the all-Laurent n=0 model. In the special fibre the remaining prime is exactly (pi,a,b); no closedness assumption on x is inserted.

Step 6 is the explicit square-zero obstruction at the generic origin: both coordinate images must lift e, hence their product is e^2 in F[e]/(e^3), independent of any choices on coefficients. It tests every neighbourhood since these Artinian spectra have one point. This is a few-line calculation from the cited formal-smoothness definition, not a new lemma to enqueue. F is the fraction field of R', and the injection R into R' supplies K into F. No algebraic closedness is needed for this obstruction.

Step 7 uses the exact universal openness statement of `lem-weil-pbc-flat-lfp-open` (morphisms.tex 01UA), the definition of etale as flat and locally finitely presented, etale base change from the first clause of `lem-weil-pbc-etale-base-change-finite-limits` (02GO), and the pointwise smoothness comparison already checked in step 5. The open image contains every generization of the special origin, including its generic nodal point; a point above that image point belongs to U_K. Applying the pointwise equivalence first to p_K and then q_K contradicts step 6. If the chosen point is away from the origin of a zero chart, restricting to D(a) or D(b) gives the n=0 model instead. I checked that source restriction uses the stated open-immersion/composition lemma and target restriction is an actual etale base change. Thus the assertion that the zero model is unnecessary covers smooth x as well as nonsmooth x.

Small cases checked: empty special fibre is vacuous; ab=0 with singular generic fibre is permitted by the first conclusion; ab=pi has n=1 and a nonsmooth special-fibre origin despite regular total space; ab=pi^2 is also allowed; ab=1 is smooth and supplies n=0; the zero chart away from its origin becomes that same n=0 chart. The obstruction and unit correction are unchanged in characteristic two. No connectedness, properness, quasi-compactness, excellence, completeness or perfectness enters any step. All steps are below 2000 characters. Every non-elementary input is an existing cited statement, and all 15 quotations were checked as literal substrings of those statements. Tool uses are declared in split_report for the generic off-unit smoothness and etale-permanence lemmas, without changing maintainer-owned tool_uses.

## Unfinished work

None in the requested one-level split. The reused unsplit normal-form node remains its own stage-1 item; its proof is not moved into a fresh equivalent node.
