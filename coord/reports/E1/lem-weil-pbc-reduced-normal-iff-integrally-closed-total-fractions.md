# Worker report: lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions

1. Files written:

   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions.json`: five-step split of Stacks Algebra Lemma 030C.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-normal-ring-integrally-closed-total.json`: new unsplit statement node for Tag 034M; Mathlib searches found only localization/domain ingredients.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-product-integral-closure.json`: new unsplit statement node for Tag 0CY9; Mathlib has the binary `IsIntegral.pair_iff` ingredient but no finite-product closure theorem.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-product-normal.json`: new unsplit statement node for Tag 0CYA; Mathlib has product-spectrum ingredients but no normal-ring notion/theorem.

2. Attachments: none. No Lean declaration was attached.

3. WANTED: none; the Stacks source is present and was read at the cited labels.

4. The original item statement was retained. The imported empty proof was split along 030C: decomposition of the total ring of fractions, normal implies integral closedness (034M), idempotent decomposition, coordinatewise integral closure (0CY9), and finite-product normality (0CYA). The first step explicitly checks that the localization is reduced and handles the zero-ring case. Existing nodes were searched by tag and concept before creating the three supporting nodes. Whole-blueprint searches by the tags and the notions found no equivalent blueprint statement; the nearest blueprint ancestor is `lem-weil-pbc-normal-constant-generic`, proof second paragraph (06DI).

5. Checks: `python3 tools/review_split.py lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions` passes. `python3 tools/check_dag.py --cycles` reports zero cycles and seven pre-existing reachability warnings unrelated to this item. No Lean was written or built.

## Review by E1

I read Algebra Lemma 030C (`lemma-characterize-reduced-ring-normal`) and its proof, together with 034M, 0CY9, and 0CYA at their exact labels. The item retains the reduced finite-minimal-prime hypothesis and the three equivalent conclusions. The three new nodes are smaller support facts with self-contained hypotheses and exact source labels; their definition citations match normality, localization, and integral closure. Searches in the current DAG found no existing node with these statements, and the recorded Mathlib searches are ingredients rather than false one-line matches.

Step 1 checks the reduced zerodivisor description, localization prime correspondence, field factors, reducedness of the total quotient ring, and the finite product decomposition, including the zero-ring case. Step 2 uses the new normal-ring total-fraction statement and the ideal of denominators argument to prove integral closedness. Step 3 checks the integral idempotents and factor domains. Step 4 uses the finite-product integral-closure node coordinatewise, and Step 5 uses finite-product normality. Each non-elementary fact is cited by a node whose statement supplies it; the source's local-to-global argument is written in the steps. I checked zero ring, one factor, and a product with zero factors, and the worker's explicit reducedness repair resolves the possible nilradical gap. No A-F issue remains.
