## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-immediate-catenary.json`: item split, statement unchanged; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim cited-statement passages for every step/dependency pair.
- `searches.jsonl`: searches made by the required search command, including preliminary branch-lemma searches. Those preliminary results are retained even though the existing criterion made new branch nodes unnecessary.

## Attachments

None. Searches for the exact blueprint tag, catenarity and geometric/immediate specialization in `WeilConjectures/` of slopmaster2 found no declaration stating this item. The upstream master source was also checked and was not used as finished-proof evidence.

## WANTED:

None.

## Audit of the original node

The statement agrees with Illusie–Laszlo–Orgogozo, Exposé XIV, Definitions 2.1.1–2.1.2 and Proposition 2.1.4, printed pp. 209–211 (PDF pp. 215–217). Proposition 2.1.3 supplies its strict-local branch interpretation. I also read Lemmas 2.1.5–2.1.6 and the proof of 2.1.4, so the universally catenary hypothesis in the converse was checked against the actual proof, rather than guessed from dimension invariance.

The item originally had no proof. DAG and whole-blueprint searches found `lem-per-immediate-specialization-criterion`, already in the same unit, stating a slightly stronger version of the required geometric/Zariski equivalence. The split reuses that node. It does not create a replacement stating one of the item's clauses. The affine saturation interpretation is written out in the item. No source or statement error was found; nothing remains unfinished in this one-level split.

## Not duplicates

`lem-per-geometric-immediate-catenary` vs `lem-per-immediate-specialization-criterion`: these are two existing nodes with substantially overlapping statements, both citing Exposé XIV Proposition 2.1.4. The criterion also gives the forward implication without universal catenarity and asserts the closure dimension for every lift. I cite that stronger existing node for the equivalence and prove the prime-chain formulation explicitly; I create no duplicate. The maintainer can consolidate the two existing nodes if appropriate, but editing or merging the other item is outside this delivery.

## Review by NJ

I read the cited Gabber pages, the item, its chapter and unit records, the nearest blueprint ancestor and its regular-unit descendant, and every cited node's statement. The item assumes a Noetherian universally catenary scheme, distinct comparable points, and no regularity, field-of-definition, or coefficient condition. All of these match Exposé XIV 2.1.4. The geometric specialization convention is the map between strict localizations of Definition 2.1.1, and its dimension is Definition 2.1.2. The statements of the existing criterion use that same convention and explicitly give independence of the geometric point. There are no new statements to review against B1–B10.

Step 1 cites `def-weil-pbc-krull-dimension-ring`, whose statement defines dimension by lengths of strict prime chains. I checked the argument directly on an affine chart: every generalization of x belongs to the chart, and localization after quotient identifies the primes of R with the interval between the primes p and q. Because y differs from x, R is a nonfield local domain and the zero-to-maximal chain is strict. No intermediate prime therefore gives exactly dimension one, and an intermediate prime gives a chain of length two. This is an elementary unpacking of spectra, quotient/localization and the cited definition, not an invocation of a hidden dimension theorem.

Step 2 cites `lem-per-immediate-specialization-criterion`. I opened its statement and copied its concluding equivalence into `citations.json`: it states that the immediate geometric specialization exists exactly when the local reduced closure has dimension one. Thus the step does not try to deduce existence from its part (a), which alone quantifies over every lift and would leave an existence gap. Its universal-catenarity hypothesis only requires an affine cover; the item's hypothesis on every affine open supplies that. Its Noetherianity and closure-relation hypotheses are exactly the item's. It requires neither excellence nor any of the coefficient restrictions in other potential-duality lemmas.

Step 3 uses the same criterion's converse for a specified geometric specialization. Its image is a point above y with closure dimension one, exactly the hypothesis of part (b); the resulting local dimension-one statement excludes an intermediate prime by Step 1 on any chosen affine neighbourhood of x. The step uses neither the proof of the criterion nor a construction hidden in it. I checked that the criterion has no dependency path back to the item, and it belongs to the same unit, so no off-unit tool-use declaration is needed.

I tested the logical edge cases on a field (there are no distinct comparable points), a DVR k[[t]] (the generic-to-closed pair is immediate), and k[x,y] localized at (x,y) (an intermediate height-one prime prevents generic-to-closed immediacy). Reducibility and nilpotents cause no extra assumption: Step 1 passes to the reduced closure of y, rather than claiming the entire scheme is integral. The converse is applied with universal catenarity and never inferred just from equality of total dimensions under strict henselization. All proof steps are shorter than 2000 characters.

I searched the whole DAG by catenarity, strict henselization, dimension, completion and source places, and ran `tools/blueprint_refs.py` searches for catenary, henselization, equidimensional, completion, Ratliff, one-dimensional and the numbered branch lemmas. No blueprint node states this comparison; the existing non-blueprint criterion supplies it. Mathlib searches for the item returned generic specialization/order and Henselian-ring declarations, but no immediate-geometric-specialization equivalence. I read the hits; preliminary branch searches likewise returned completion infrastructure and one-dimensional-domain results with different conclusions. The exact query texts and results are recorded by `msearch.py`; there is no invented search and no new-node leaf claim.

The first complete server dry run passed at 4aedcc6ee8. This report was then aligned with the final three steps (the preliminary draft report described a different step order); the report-only update is included in the final rerun and delivery.
