# Stage 1 report: `lem-weil-pbc-grothendieck-existence-devissage`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-grothendieck-existence-devissage.json`: split Lemma 088A into five proof steps following the source.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-grothendieck-existence-easy.json`: new public unsplit statement for Lemma 0889, used by the fourth and fifth steps.
- `coord/reports/G1/lem-weil-pbc-grothendieck-existence-devissage.md`: this report.

## Sources and corrections

The proof follows Cohomology of Schemes, Lemma 088A (coherent.tex lines 6955--7012). The closed-immersion equivalence is the existing 087T node; the annihilation transfer is the existing 0888 node; and the newly added 0889 node states the easy algebraization lemma used by the source. The imported statement already matches the source and was not weakened or changed.

The 0889 child is statement-only while unsplit, introduces all objects and both orientations of the source lemma, carries the exact Tag 0889 source location, and records LeanSearch, LeanFinder, and grep searches. Mathlib has ring-level adic-completion results but no coherent formal-module algebraization theorem.

## Review by G1

I checked each parent step against the source proof. Step 1 uses 087T to identify coherent modules on $X_e$ with modules on $X$ annihilated by $\mathcal K^e$, and consequently transports hypothesis (1) to the required formal subcategories. Step 2 constructs $\mathcal G_e$ and its transition isomorphisms from the quotient systems. Step 3 applies the exact commutative-algebra content of 0888 twice, giving the source's $\mathcal K^{2t}$ and $\mathcal K^{4t}$ bounds. Step 4 applies 0889(1), and Step 5 uses its uniqueness after reduction modulo $\mathcal I^n$ to obtain a compatible completion isomorphism. Every source tag in the proof is carried by a cited node, the new child has `created.item` equal to this item, and both nodes retain unit `sk-thm-p1`. No Lean was written or compiled.

## Validation

`review_split.py`, `check_dag.py --cycles`, and `git diff --check` are run before delivery. Existing reachability notices are unrelated to this item.
