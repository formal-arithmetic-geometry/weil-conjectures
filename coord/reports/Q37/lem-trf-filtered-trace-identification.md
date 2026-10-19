# Q37: lem-trf-filtered-trace-identification

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-filtered-trace-identification.json`: existing statement, now split into five proof steps; statement and dependencies retained; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every step.
- `searches.jsonl`: the four required Mathlib searches actually run for this item.
- No Lean files, compiler, Lake, or global build operations were used.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` for the item id, the blueprint tag, filtered pre-evaluation, and Verdier trace-identification terminology. No sorry-free project declaration states this item. The generic filtered and trace declarations found are not an exact attachment.

## WANTED

None. The cited Varshavsky PDF is present at the source path in the node.

## Issues found and repaired

No `STATEMENT-DISPUTED` issue was found. The imported statement has the finite coefficient, constructibility, admissibility, filtered-category, exceptional-adjunction, evaluation convention, and filtration-degree-zero clauses required by the source route; I did not add hypotheses or weaken its conclusion. The imported node had no proof. I supplied the filtered-lift construction, specialization and evaluation, the arrow-by-arrow comparison with the external-duality trace map, and the underlying-map/filtration-zero conclusion. There are no new-node duplicate pairs; all inputs are existing DAG statements.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs. I searched the DAG and current blueprint for filtered pre-evaluation, external-duality trace compatibility, and Lemma 5.3.2; the existing nodes `lem-trf-filtered-pre-evaluation`, `lem-trf-filtered-operations-hom`, and `lem-trf-trace-map-from-external-duality` cover the auxiliary assertions without restating this item.

## Mathlib searches

I ran `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch with the exact queries recorded in `searches.jsonl`. LeanFinder and LeanSearch returned generic evaluation, tensor, chain-map, and ordinary module-trace declarations. Loogle returned only natural-transformation congruence declarations; grep over `Mathlib/` found no trace-map/external-duality/evaluation compatibility declaration. These are no-match searches, and the item is not a Mathlib leaf.

## Review by Q37

I read the item, `sec-trace-formula.json`, unit `sk-i-curve-zero.json`, and the full statements of all ten proof dependencies. I read Varshavsky's Lemma 5.3.2 proof on pp.42–43 and §§5.2.1–5.2.2 on pp.41–42. The source first constructs the filtered lift of the trace-pre-evaluation map, then identifies its degree-zero restriction after evaluation with the ordinary trace. The five delivered steps follow that order.

Step 1 uses `def-trf-bounded-filtered-derived-category` for the finite filtration and forgetful/graded constructions, `lem-trf-filtered-operations-hom` for filtered lifts whose forgotten maps are the ordinary six-functor transformations, and the coefficient/admissibility nodes for the domains. I checked that the stated finite-Tor constructibility and exceptional-admissibility hypotheses are exactly those used; no ambient unrestricted exceptional adjoint is introduced.

Step 2 uses the statement of `lem-trf-filtered-pre-evaluation`, which explicitly supplies `T''^F`, its underlying `T''`, naturality, and the exceptional-Hom/Künneth/diagonal/fixed-square/symmetry ingredients. `thm-trf-verdier-duality` supplies the compatible external-duality comparison and evaluation compatibility. I used those statements rather than facts hidden in either node's proof.

Step 3 specializes the two independent variables to `\widetilde K` and applies the evaluation from `def-trf-dualizing-complex`. The pre-evaluation statement places the target coefficient and dualizing object in filtration degree zero, while `lem-trf-filtered-operations-hom` says forgetting the filtered lift gives the ordinary pre-evaluation and evaluation maps. This verifies the exact source and target of `\widetilde\tau'` and the `[0]_{\mathrm{fil}}` convention.

Step 4 is the substantive comparison. I read the complete composite in `lem-trf-trace-map-from-external-duality`: it uses `\xi`, the diagonal transpose, fixed-square base change, `Rd^!\omega_X\simeq\omega_F`, and global sections. I compared it with the displayed composite in `lem-trf-filtered-pre-evaluation`; both have the same exchange, inverse Künneth, diagonal unit, base-change, signed symmetry and evaluation arrows. `thm-trf-verdier-duality` states compatibility with evaluation, and `thm-trf-dualizing-complex-composition` supplies the exact dualizing comparison. Naturality of adjunction transposes therefore identifies the composites, proving (a)=(b). The trace-class definition confirms that this map is the map used under the exceptional-adjunction identification.

Step 5 uses the global filtered-Hom formula in `lem-trf-filtered-operations-hom` and the degree-zero placement from `def-trf-bounded-filtered-derived-category`. Its target is concentrated in filtration degree zero, so forgetting the filtered map gives exactly the ordinary composite already checked in steps 3–4. The filtration index labels the target object and introduces no cochain shift, as required by the statement.

I checked edge conventions on the zero filtered object, a one-step filtration, and an ordinary object placed in degree zero: all constructions reduce to the ordinary pre-evaluation/evaluation composite and the target remains in filtration degree zero. Every citation quote in `citations.json` is a verbatim substring of the cited statement. No proof step exceeds 2000 characters, no step cites a node for information absent from its statement, and the dependency graph has no cycle through this item. No SGA source was used.
