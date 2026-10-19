Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-reduced-total-fractions-field-extension.json` — existing statement node, now split; no new nodes; Mathlib verdict remains no exact match.
- `citations.json` — verbatim citations for all five proof steps.
- `report.md` — this report.

Attachments: none. No sorry-free project declaration with the exact item statement was found in `WeilConjectures/` of the slopmaster2 and master reference checkouts.

WANTED: none.

The imported statement was retained. It is the affine fraction-ring calculation used in Stacks Tag 0C3N, specialized to a finite-type domain over a field. The finite-type hypothesis is part of the source context; the ring argument below only needs the domain and field-extension hypotheses. No source or blueprint error was found, and no duplicate node was created. The existing Mathlib searches and the Q29 `searches.jsonl` log record no exact Mathlib theorem for reduced total quotient rings after scalar extension.

## Review by Q29

I read the complete item node, the `sk-p-dl-a1-perverse` unit and `sec-deligne-laumon-a1` chapter records, the inherited blueprint ancestry, and the second proof paragraph of `literature/stacks-project/varieties.tex` at Tag 0C3N. I also checked the exact declarations searched in the source trees; none states this item without `sorry`.

Step 1 uses `lem-weil-pbc-module-over-field-flat` for flatness of a field extension as a module, `lem-sc-flat-going-down` for prime-chain lifting under the scalar-extension ring map, and `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes` for the characterization of nonzerodivisors in a reduced ring. Their statements give exactly the flatness, going-down, and minimal-prime facts used. I verified the hypotheses: (M/L) is a nonzero vector-space extension, the tensor map (B_L\to B_M) is split injective by a coefficient functional, and minimal primes correspond after quotienting by the nilradical. Going down then shows that a minimal prime upstairs contracts to a minimal prime downstairs, so a downstairs nonzerodivisor remains one upstairs.

Step 2 uses the localization definition `def-weil-pbc-module-localization`; its fraction representation and zero criterion are exactly what is used to construct and prove injectivity of (Q_L\to Q_M). Step 3 uses the same localization definition, the tensor-product universal property `def-weil-pbc-module-tensor-product`, and the field-flatness node. I checked that a nonzero (s\in A) stays regular after tensoring and after reduction, so the displayed formula for (	heta_L) has a valid denominator.

Step 4 again uses the localization zero criterion. Every tensor fraction is reduced to a common denominator; vanishing in (Q_L) forces its numerator to vanish in (R_L), hence to be nilpotent in (B_L), while nilpotents map to zero in the reduced localization. This proves both inclusions for the kernel and checks the nilpotent edge case explicitly. Step 5 uses only the tensor and localization definitions: checking represented fractions on pure tensors proves the tower and principal-localization compatibilities by their universal properties.

I checked the small cases (A=k), (L=k), (L=M), a polynomial domain (A=k[x]), and an inseparable scalar extension where (B_L) acquires nilpotents. In each case the reduction map, total-fraction injection, and nilpotent kernel behave as stated. The proof cites no SGA source, adds no new node, and introduces no cycle. The only off-unit inputs are the three generic algebra facts recorded in `split_report.tool_uses`.

What remains unfinished: nothing.
