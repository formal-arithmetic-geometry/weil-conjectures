# Worker report: lem-coef-walking-module-weight-cells

## Files written

- `dag/nodes/sec-six-functors/lem-coef-walking-module-weight-cells.json`: repaired item proof; statement unchanged.
- `dag/nodes/sec-six-functors/lem-coef-free-module-orbit-cell-filtration.json`: repaired statement-only supporting lemma; Mathlib searches found only generic relative-cell and skeleton APIs, so verdict no match.
- `citations.json`: refreshed verbatim citations for all proof steps.

## Attachments

No finished slopmaster2 declaration was found. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: lem-coef-walking-module-weight-cells)` and no matching walking-module declaration.

## WANTED

- WANTED: Emily Riehl, *Adjunctions*, Definition 6.1.6, Lemma 6.1.8, proof of Corollary 6.2.3, Observation 6.2.4 and Proposition 5.3.3, for the item and `lem-coef-free-module-orbit-cell-filtration`; the cited PDF is online at `https://emilyriehl.github.io/files/adjunctions.pdf` and is not archived in `literature/`.

## Existing-node and Mathlib searches

I searched the whole DAG and blueprint for free-orbit, ordinal-sum, cellular-weight and projective-cell statements. No existing node or blueprint statement gives the corrected free-orbit criterion. The required searches for the revised criterion are recorded in `searches.jsonl`; Mathlib supplies generic `RelativeCellComplex` and skeletal declarations but no walking-module or free-orbit criterion.

## Repair and source issues

The imported item statement remains unchanged. The returned review correctly identified that the old Step 3 used an invalid terminal-prefix reduction: a simplex `j(a)=a⊕id_[0]` can lie in the orbit of `[0]` even when that test finds no such prefix. The old relative Step 4 also used an undefined “first nontrivial terminal fibre” order. I repaired both by using the maximal common **left** ordinal summand, with an explicit uniqueness argument, epi-mono factorization into a unique surjective degeneracy and nondegenerate representative, and an ordinary dimension filtration. For the relative map, I characterize `j(D)` by the terminal singleton identity summand; this condition is preserved by left `D`-action, so outside orbits are disjoint from the base. The new supporting node now requires unique expressions `m·(θ*σ)`, disjoint free orbits, and boundaries in the earlier stage, which is the exact hypothesis used by Steps 2–4. No SGA source is used, and no Lean or compiler tool was run.

## Review by N4

I reread the item, the chapter and unit records, the imported blueprint ancestry, the coherent-monad definition, and the returned review. Step 1 uses only the ordinal-sum and nerve clauses of `def-coef-coherent-monad-modules`; equivariance and vertex bijectivity are direct finite-ordinal checks. Step 2 now cites the corrected criterion and explicitly matches each hypothesis to the pushout construction, including zero-cells and limit unions. In Step 3 I checked the finite-ordinal left-summand cut, its uniqueness, and the epi-mono factorization; the resulting expression is exactly the `m·(θ*σ)` expression required by the new node. Step 4 uses the ordinary dimension filtration, so every proper face is in the previous stage. I separately checked that the terminal-singleton identity-summand characterization of `j(D)` is preserved by prepending and therefore prevents an outside orbit from meeting the base. Step 5 checks zero-dimensional cells, continuity at limits, and the identification of left `D`-modules with weights for the one-object simplicial category. Every cited quote in `citations.json` is copied verbatim from the cited node statement. I also tested the revised normal form on the empty ordinal, the singleton, `j(a)`, and a map with a nontrivial terminal fibre; the counterexample from the return is handled by the left-summand cut. No duplicate or cycle was introduced.
