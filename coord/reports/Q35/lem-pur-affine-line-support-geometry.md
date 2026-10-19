Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-affine-line-support-geometry.json`: the item split into five proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node at every step.
- `report.md`: this report.

Attachments: none. I searched the read-only slopmaster2 `WeilConjectures/` and `Comparator/` trees for the exact blueprint id and for the finite-type, Noetherian, affine-line, and quasi-compact-open terminology. No declaration states this item exactly with a finished proof.

WANTED: none.

Findings and corrections: the imported statement is well-typed and agrees with the first paragraph of the current main-20261015 `lem-pur-gysin-structure` proof. No statement or hypothesis was changed. The proof uses the existing DAG leaves `lem-weil-pbc-finite-type-over-noetherian`, `lem-sfb-finite-type-composition-base-change`, `lem-weil-pbc-spec-localization-away-basic-open`, `lem-weil-pbc-affine-scheme-qcqs`, and `lem-weil-pbc-qc-open-immersion-finite-type`; no duplicate node was created. The field-base Noetherian assertion is checked directly from the ideal structure of a field. Edge cases checked include $Y=\\varnothing$, $Y=\\operatorname{Spec}k$, the zero-variable identity case, and nonreduced affine charts: all arguments remain valid, and $D(t)$ is empty when the chart is empty.

## Not duplicates

None: no new nodes were created.

## Review by Q35

I read the item node, `sec-smooth-purity` chapter, `sk-prop-a1-kummer` unit, the current main-20261015 `lem-pur-gysin-structure.proof.md`, and every statement cited in the five steps. Step 1 uses the exact conclusion of `lem-weil-pbc-finite-type-over-noetherian`; its hypothesis is met because a field has only the zero and unit ideals, so `Spec k` is Noetherian. Step 2 checks the affine chart `Spec R[t]` from `def-sbc-affine-space`, observes finite generation by `t` under `def-weil-finite-type-morphism`, and uses the composition clause of `lem-sfb-finite-type-composition-base-change` to obtain finite type over `k`. Step 3 uses the stated principal-open chart, the localization-homeomorphism statement of `lem-weil-pbc-spec-localization-away-basic-open`, and the affine quasi-compactness conclusion of `lem-weil-pbc-affine-scheme-qcqs`; this verifies the quasi-compactness condition for every affine target open of `j`. Step 4 applies the exact statement of `lem-weil-pbc-qc-open-immersion-finite-type` and then finite-type composition. Step 5 applies the Noetherian finite-type conclusion separately to `X` and `U`, with the base hypothesis already checked in Step 1. Every citation quote in `citations.json` is copied verbatim from its node statement. I also checked the empty scheme, the identity case, and a nonreduced ring chart, so no hidden nonemptiness, reducedness, or separatedness assumption entered the proof.

Unfinished work: none.
