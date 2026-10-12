## What changed

Replaced the sole sorry of `Sheaf.AlgebraicGeometry.ProperCoproduct` by a complete proof.
The coprojection clauses use Mathlib instances and `isCompl_range_inl_inr`.
For properness, factor `coprod.desc p₁ p₂` as `coprod.map p₁ p₂` followed by
`coprod.desc (𝟙 S) (𝟙 S)`. The first factor is proper by
`IsZariskiLocalAtTarget.coprodMap`; the fold map is finite and hence proper.
Coproduct extensionality verifies the factorization, and proper composition finishes.
Updated the existing node's proof, proof dependencies and proof origin to this route.
All existing signatures, visibility and imports are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.proper_coproduct_two`
(node `lem-weil-pbc-proper-coproduct`), the only original hole: 1 of 1 proved.
No sorry remains; no holes added and no statements split off.
The proof uses only proved Mathlib facts. No empty-scheme or nonempty-base
hypothesis is needed; the factorization also works when either component or the base is empty.

## No longer needed

No imports removed: the two public Mathlib imports support the unchanged statement.
The proof no longer needs the following old proof dependencies:

- `def-weil-open-immersion` as a proof dependency (retained as a statement dependency).
- `def-weil-finite-type-morphism`.
- `def-pc-fibre-product`.
- `lem-weil-pbc-open-fibre-product`.
- `def-weil-closed-immersion`.
- `lem-weil-pbc-diagonal-immersion`.
- `lem-weil-pbc-immersion-closed-image-closed-immersion`.

These are Mathlib-backed nodes, with no additional Sheaf proof modules imported or needed.
The scheme-coproduct-family node remains realized through the binary Mathlib facts.
No unit statement or realized unit step is pruned: this auxiliary node is absent from
`dag/units/sk-thm-p1.json`'s realized statements and steps.

## Where the brief, the DAG or earlier work was wrong

The planned separate finite-type, universal-closedness and diagonal arguments are unnecessary.
The earlier search correctly found no direct proper `coprod.desc` theorem, but missed the
factorization through the target coproduct and the existing target-local `coprodMap` theorem.
The existing declaration docstring retains the original plan; the updated node records the
proof actually used. No statement or definition correction was required.

## Second reading by N1

1. Compared the delivered module against the repository version. The theorem signature,
   visibility, and definitions are byte-for-byte unchanged; only the proof body differs.
   Verdict: pass.
2. Compiled the sandbox module with `lcompile.py`; it succeeds without errors or warnings.
   The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
   `extern`. The proof uses the Mathlib coproduct open-immersion/complement facts,
   target-local properness of `coprod.map`, and properness of the finite fold map.
   Verdict: pass.
3. The existing theorem is the only declaration and no statements were split off. Its
   statement is unchanged and no new node is introduced. Verdict: pass.
4. The factorization through `S ⨿ S` is shorter than the former finite-type,
   universally-closed, and diagonal argument, while retaining the binary coproduct
   route. The public imports remain necessary and no unused import was found.
   Verdict: pass.
5. The DAG proof steps, dependencies, and origin match the proof body; the unit's
   realized route is unchanged. Verdict: pass.

Changed only the report by recording this review; no repair to the Lean proof or DAG was
needed.
