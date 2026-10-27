## What changed

Proved `WeilConjectures.PurityFiniteSetting.exists_purityScalarLineNormalization`
in `Sheaf.Paper.NormalizedVectorPurityScalarLineWitness`, preserving its signature.
Added the proof-only import `Sheaf.Paper.FiniteTateScalarSourceExistence`.
Transported the annihilator through the coefficient homomorphism and the global unit
through each germ homomorphism. Selected degree one of the existing balancing family
and specialized its generator formula at target coefficient one. Updated the item node
to record this route. No definitions, instances, attributes, or public imports changed.
The delivered file compiles cleanly through `lcompile.py` in 8.4 seconds.
Searches through `msearch.py` (Lean Finder, Loogle, and Mathlib grep), plus project
source searches, found no shorter direct Mathlib result for this sheaf comparison.

## Proved and sorry left

Closed the sole hole, `WeilConjectures.PurityFiniteSetting.exists_purityScalarLineNormalization`
(node `lem-pur-normalized-vector-purity-scalar-line-witness`). Added zero holes and zero
split-off statements. No sorry remains in the delivered module. The proof uses the
existing theorem `finite_tate_scalar_source_normalization_exists`; its already-existing
hole is outside this delivery.

## No longer needed

The planned dependency `lem-pur-finite-tate-scalar-source-normalization`, module
`Sheaf.Paper.FiniteTateScalarSourceNormalization`, is unnecessary for this proof:
uniqueness, flat-single comparison, shifted-line and derived source compatibility
are not needed to obtain the degree-one ordinary comparison. Its existing construction
lemma `lem-pur-finite-tate-scalar-source-existence` already gives the required balancing.
No existing import was removed; the statement still needs the sole public import
`Sheaf.Paper.VectorPurityFiniteReduction`. No assertion is made that the normalization
module is globally unused by other consumers.

## Where the brief, the DAG or earlier work was wrong

The original proof plan refers to a line-normalization clause, but the relevant clause
is the degree-one generator equation in `IsFiniteTateScalarBalancing`, not
`IsFiniteTateScalarLineNormalized` (which states derived single/unit and shift laws).
The construction theorem suffices without the larger normalization theorem. The current
server queue marks this item as a one-hole proof item, with no rework row or build-error
file. Edge cases introduce no extra assumption: unit transport works on every stalk
(and vacuously on an empty base), coefficient transport works for the zero ring, and
the proof uses no flatness assumption on the coefficient homomorphism.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NormalizedVectorPurityScalarLineWitness": "dec7fb3c9f4c9c3239b88c4635c965f14f034ed0"}, "results": {}, "time": "2026-10-28T03:20:34+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
