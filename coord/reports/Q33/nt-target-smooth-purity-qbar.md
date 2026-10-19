# nt-target-smooth-purity-qbar

## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/nt-target-smooth-purity-qbar.json` (eight-step repaired split); `lem-pur-condensed-tate-integral-tower.json` (statement-only frontier node); `lem-pur-condensed-tate-realization.json` (statement-only frontier node); `citations.json`. There are no Mathlib leaves.
2. Attachments: none. The exact upstream declaration is a chosen `sorry` definition in `literature/upstream-master-20261016/WeilConjectures/SmoothPurity/Defs.lean:88-92`; no sorry-free project declaration states this target.
3. WANTED: none.
4. The returned split had four non-elementary proof steps longer than 2,000 characters. I replaced those inline arguments with short steps citing the existing arbitrary-field finite smooth-adjunction and condensed exceptional-reconstruction nodes, plus the two new frontier nodes. The target statement and its hypotheses are unchanged. The route uses the current diagonal/DNC and tower/reconstruction blueprint and does not use SGA 4 or SGA 4½.
5. Remaining work: the two new statement-only nodes require later stage-1 splits; this delivery handles only the requested one-level split.

## Review by Q33

I read the exact target source `literature/upstream-master-20261016/WeilConjectures/SmoothPurity/Defs.lean`, including its imports and declaration signature. It quantifies a prime ell, a positive-characteristic field k with ell different from the characteristic, separated finite-type objects X and Y over Spec k, a smooth pure-relative-dimension morphism f, the chosen bounded-constructible upper-shriek, the condensed tensor unit, and the actual `tateTwistDerived` endpoint. The node retains all of these and the direction of the chosen isomorphism.

For step 1 I checked `sk-def-sfb-dc-setting`, `prop-weil-pbc-qbar-condensed-two-colimit`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-kun-dimension-finite-type`, and `lem-pur-condensed-exceptional-reconstruction`. Their statements supply the actual finite-extension-valued condensed coefficient category, the chosen compactification/right adjoint, and the Noetherian and finite-dimensional hypotheses used in the setting. The unit is treated as the tensor unit of that category.

For steps 2 and 3 I reread `lem-pur-finite-smooth-adjunction-general-base`. It states the arbitrary-ground-field finite coefficient exceptional adjoint, the diagonal/DNC/Kummer-normalized orientation, preservation of the constructible finite-Tor domain, the counit-defined reduction comparisons, and their quotient cocycle. This is exactly what the shortened steps take from it, so the old finite-field-only Qbar theorem is not substituted for the target field.

For step 4 I read the new `lem-pur-condensed-tate-integral-tower` statement and the definitions it cites: the normalized tower, root-power transitions, finite-level gamma maps, strict reductions, compatible etale-origin witnesses, and completed integral reconstruction are all stated there. The step therefore no longer hides the tower construction in a long paragraph. For step 5 I read the complete statement of `lem-pur-condensed-exceptional-reconstruction`; its case (b) is precisely the common-degree good-truncation comparison to the chosen `boundedConstructibleUpperShriek`, including the geometric counit. The unit multiplication comparison in step 6 uses the cited ringed-topoi tensor/pullback statement and has the displayed inverse maps.

For steps 7 and 8 I read the new `lem-pur-condensed-tate-realization` statement and its cited definition and realization nodes. It states the finite-level coefficient quotient and roots-of-unity identifications, the inverse-limit Tate line, scalar realization, balanced tensor comparison, and the d=0 identity. Step 8 only composes this endpoint map with the exceptional comparison from step 6; its inverse is the explicitly written composite. All citation quotes in `citations.json` are copied verbatim from the cited node statements.

I searched the whole DAG and current blueprint for both new statements and for their coefficient/tower keywords. The existing finite smooth-adjunction node is broader in its finite purity and reduction clauses, while the tower node adds completed reconstruction; the existing condensed realization and Tate-definition nodes provide ingredients but do not state the combined endpoint comparison. The new Tate-realization node has no smoothness, exceptional functor, or purity conclusion, and the new tower node has no condensed Qbar endpoint, so neither restates the target. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` for the target and each new node; the returned declarations were generic smooth, inverse-system, tensor, or condensed constructions and none matched.

I checked edge cases d=0 (identity orientation and the endpoint comparison is the unit), n=1, the zero n=0 Tate term, the identity morphism, empty schemes, and an arbitrary non-finite ground field such as F_p(t). These checks found no statement error. No Lean files were written and no compiler, Lake, or build tool was run.

## Not duplicates

lem-pur-condensed-tate-integral-tower vs lem-pur-finite-smooth-adjunction-general-base: the existing node gives finite exceptional purity and reduction maps; this node additionally states strict normalized towers and completed integral reconstruction.
lem-pur-condensed-tate-integral-tower vs lem-pur-condensed-exceptional-reconstruction: the existing reconstruction node assumes a supplied coherent tower and compares it to the condensed exceptional adjoint; this node constructs and reconstructs the specific Tate/unit towers before that comparison.
lem-pur-condensed-tate-realization vs def-pur-condensed-tate-twists: the existing node defines the target Tate module system; this node proves its identification with the reconstructed integral tower after coefficient realization.
lem-pur-condensed-tate-realization vs lem-weil-pbc-condensed-e-realization: the existing node gives generic finite-coefficient realization; this node specializes the coefficient maps and balanced tensor comparison to the geometric Tate tower.
lem-pur-condensed-tate-realization vs nt-target-smooth-purity-qbar: the new node has no smooth morphism or exceptional inverse image and only identifies the coefficient endpoint used by the target proof.
