# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-derived-functor-commutes-derived-limit.json`: completed the three-step split and replaced the bounded-below citation with the unbounded homotopy-limit mapping theorem.
- `dag/nodes/sec-picard-framework/lem-pc-homotopy-limit-map.json`: statement-only project theorem, attached to the sorry-free declaration `CategoryTheory.Pretriangulated.IsHomotopyLimit.map`.
- `citations.json`: verbatim statement quotes for every proof dependency.

## Attachments

`CategoryTheory.Pretriangulated.IsHomotopyLimit.map` belongs to `lem-pc-homotopy-limit-map`.

## WANTED

WANTED: `literature/stacks-project/injectives.tex`, Tag 08U1, for the right-derived-functor comparison; the local literature checkout lacks this source and the proof was read from the available review copy.

## Not duplicates

`lem-pc-homotopy-limit-map` vs `lem-weil-derived-limit-existence`: the new node states preservation of Roos cones by a triangulated product-preserving functor, while the existing node states existence, uniqueness, and termwise-product computation of derived limits.

## What was wrong in the earlier attempt

The earlier split cited `lem-weil-pbc-derived-direct-image-triangulated`, whose statement is only a bounded-below derived direct image and does not provide the unbounded right-derived functor structure required by this item. I replaced it with the project declaration `IsHomotopyLimit.map`, whose statement exactly supplies the Roos-triangle transport once product preservation is established. The generic derived-limit existence node is an off-unit tool and is declared as such in `split_report.tool_uses`.

## Review by G1

I read Stacks Tag 08U1 (`literature/stacks-project/injectives.tex`, label `lemma-RF-commutes-with-Rlim`) and checked the item hypotheses: a scheme, an additive left exact functor with a right derived functor, countable-product preservation, and a countable inverse system in the derived category. Step 1 uses only `def-weil-derived-limit`; its quote gives the derived-limit triple and hence the Roos triangle. Step 2 uses `lem-weil-derived-limit-existence`, whose statement explicitly says that products in the derived category are represented termwise, and `def-sp-left-exact-additive`, whose statement explicitly defines right derived functors through injective resolutions; the remaining identification is the stated product-preservation hypothesis applied termwise. Step 3 uses `lem-pc-homotopy-limit-map`, whose attached declaration states that an additive triangulated functor preserving tower products maps homotopy-limit cones to homotopy-limit cones, together with the existing product and derived-limit statements to identify the image cone and its vertex. Every citation quote is copied verbatim from the cited statement.

For the new node I read `WeilConjectures/CategoryTheory/Triangulated/HomotopyLimit.lean` lines 187–214 and verified the declaration is sorry-free in slopmaster2. I searched the DAG and blueprint for homotopy-limit mapping statements and found no duplicate. The Mathlib searches were run and recorded in the node; Mathlib has no project-specific `IsHomotopyLimit.map`. Small checks include a constant tower, where the map reduces to preservation of the split Roos triangle, and the identity functor, where the conclusion is immediate.

The source copy is unavailable locally, so the report records the required WANTED line. No Lean files were changed or compiled.

## Second reading by G1

- Item statement: checked Tag 08U1, label `lemma-RF-commutes-with-Rlim`, against the scheme/module specialization; additivity, product preservation, existence of `RF`, and the derived-limit conclusion are present. Verdict: correct specialization.
- Step 1: checked the Roos triangle and transition map against `def-weil-derived-limit`; the setup is elementary and cites the defining node. Verdict: correct.
- Step 2: checked the K-injective product model against Tag 070L and the termwise-product clause of `lem-weil-derived-limit-existence`; the missing K-injectivity fact is now cited explicitly, and the product-preservation identification is written out. Verdict: repaired.
- Step 3: checked the exactness/shift requirement against the project declaration in `RightDerivedFunctor/Triangulated.lean` lines 94-99 and the cone transport against `IsHomotopyLimit.map`; the image-product and uniqueness arguments are explicit. Verdict: repaired.
- `lem-pc-homotopy-limit-map`: checked its statement against `HomotopyLimit.lean` lines 187-214 and the attached sorry-free declaration; no duplicate in the DAG or blueprint. Verdict: valid project leaf.
- `lem-pc-ringed-space-product-kinjective`: checked the self-contained ringed-space/K-injective statement against Tag 070L; searched the DAG for existing product/K-injective statements and found only the weaker product-existence node. Small tests: a singleton family gives the original K-injective complex, and an empty family gives the zero complex. Verdict: needed and correctly scoped.
- `lem-pc-right-derived-functor-triangulated`: checked the shift and distinguished-triangle clauses against the sorry-free project instances at lines 94-99; no Mathlib declaration gives the K-injective construction. Verdict: needed and correctly scoped.

Changes made: added explicit statement-only leaves for K-injective product closure and triangulated unbounded right derived functors; rewrote Steps 2-3 to cite them and state the identifications; updated `citations.json` with verbatim quotes. The source review copy is `/home/ubuntu/c1-stacks-review/injectives.tex` because the local literature checkout lacks `injectives.tex` (WANTED retained above).

