# Stage 1 report: `lem-weil-pbc-z-localizations-dvr`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-z-localizations-dvr.json`
- `coord/reports/G1/lem-weil-pbc-z-localizations-dvr.md`

## Repair

The returned proof is now a four-step split following Algebra Definition 034W, Lemmas 0AUQ and 034X, localization prime correspondence (00E3), and the DVR criterion (00PD). Step 1 writes out the reduced-fraction proof that the PID `Z` is integrally closed. Step 2 classifies its primes and deduces dimension one and Dedekindness. Step 3 cites `lem-weil-pbc-localization-prime-residue-field-iso` for the prime correspondence, `def-weil-pbc-localization-at-prime` for the local maximal ideal, `def-weil-pbc-normal-ring` for the normal-domain identification, and the existing normal-domain and Noetherian localization leaves. Step 4 cites `lem-sc-normal-dim1-dvr`, which records the one-dimensional normal-local DVR criterion, as a generic tool use.

No new nodes were needed and no Lean files were changed.

## Sources and checks

The statement remains the imported arithmetic assertion. The proof source is `literature/stacks-project/algebra.tex`, Tags 034W, 0AUQ, 034X, 00E3, and 00PD. `proof_deps` is exactly the union of the step uses.

## Review by G1

I independently checked the returned reasons against the revised JSON. The integrally closed claim is no longer unsupported: for a reduced fraction `a/b` satisfying a monic equation, clearing denominators gives `b | a^n`, and coprimality gives `b = 1`. The prime correspondence in the localization step is explicitly carried by `lem-weil-pbc-localization-prime-residue-field-iso`, while the local and maximal-ideal description comes from `def-weil-pbc-localization-at-prime`; the normality and Noetherian assertions use their existing localization leaves. The final DVR conclusion cites `lem-sc-normal-dim1-dvr`, whose source is Stacks 00PD, and is recorded under `tool_uses` so the unit-route checker treats this standard criterion as a generic tool lemma. The statement, source, and blueprint route are unchanged, no duplicate support node was created, and the item remains a one-level split.
