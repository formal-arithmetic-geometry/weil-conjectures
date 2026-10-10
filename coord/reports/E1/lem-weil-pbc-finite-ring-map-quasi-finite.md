# lem-weil-pbc-finite-ring-map-quasi-finite

## Worker report

1. Files: dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-ring-map-quasi-finite.json (split, no new nodes) and this report. The statement and Mathlib candidate were kept.
2. Attachments: none. Searches of the read-only slopmaster2 WeilConjectures/ and Comparator/ by node id, notion, and finite/quasi-finite terminology found no exact declaration.
3. WANTED: none. Read Stacks Algebra Tags 00PM, 0H8X, 00PL and 00QA in algebra.tex, and checked their labels against tags/tags. The cited existing leaf lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum has its source in Tag 06RS; the prime correspondence is lem-weil-pbc-fibre-ring-primes-bijection.
4. The imported node had no proof. Its four steps now show that module generators are algebra generators, still span every residue-field fibre after tensoring, make each fibre spectrum discrete through the cited leaf, and isolate the point over any prime through the cited fibre-prime correspondence. The item has blueprint.same_as = [pqf-lem-finite-qf]; that blueprint node is the scheme-level analogue, so it does not replace the ring-level item.
5. Nothing remains for the worker. review_split.py passes with zero new nodes; blueprint_refs.py check passes. check_dag.py reports 18 existing reach/route errors outside this item and zero cycles.

## Review by E1

I read Stacks Algebra 00PL (definition-quasi-finite), 0H8X (lemma-quasi-finite-above-p) and 00PM (lemma-quasi-finite), plus the finite-map use in 00QA. The item has the finite-module hypothesis that yields both finite type and finite residue-field fibres; its conclusion is the isolated-point form of 00PL at every prime. The cited definition node states that exact notion. The existing fibre-prime-bijection node identifies the point over q, and the finite-over-zero-dimensional-local node states that the finite algebra over the residue field has finite discrete spectrum. I read those statements and checked their hypotheses at each application. No new node is created; the blueprint's pqf-lem-finite-qf is the scheme-level analogue rather than an exact replacement, and the Mathlib candidates do not state the item's isolated-fibre-point notion in one line.

Step 1 uses the finite module generators as algebra generators, giving the displayed polynomial surjection. Step 2 tensors their module span with kappa(p), so the fibre is finite over that field; the zero fibre causes no exception. Step 3 applies the cited discrete-spectrum statement with R=kappa(p), whose only prime is zero. Step 4 uses the cited prime bijection and the item's quasi-finite-at-a-prime definition to conclude for arbitrary q. These arguments use no unseen proof of a cited node, and the finite-type hypothesis required by 0H8X is established first. I found no A-E defect requiring worker repair.

Process report for L: a separate claimed E1 item, prop-weil-pbc-strict-henselization-stalk-formula, needs the existing cross-unit 03Q8 node sbc-lem-higher-direct-image-presheaf. `review_split.py` rejects that genuine tool unless `item.tool_uses` is set, while delivery-errors C8 reserves that field for L at merge and preflight requires review_split to pass before push. The worker found no same-unit or Mathlib replacement. Please reconcile the checker with C8 or tell E1 the authorized route; that delivery is held.
