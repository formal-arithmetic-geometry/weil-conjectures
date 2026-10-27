## What changed

The item now assembles scalar reduction from two named intermediate theorems.  The line-witness
module isolates existence and normalization of the target Tate line.  The compatibility module
isolates the fixed-witness scalar source, compact-support and mate equations.  The item obtains the
normalized target vector purity family, applies the compatibility theorem, and packages the exact
existential predicate.  All three modules compile in import order.

## Proved and sorry left

The item theorem `vectorIntegrationCounit_scalarReduction` is proved by assembling the two strict
intermediate statements and `vectorBundleNormalized`.  The two intermediate theorem proofs remain
`sorry`, each as a named public theorem with its own blueprint node:

- `exists_purityScalarLineNormalization` in
  `Sheaf.Paper.NormalizedVectorPurityScalarLineWitness`;
- `scalarReduction_compatibility_of_witnesses` in
  `Sheaf.Paper.NormalizedVectorPurityScalarCompatibility`.

## No longer needed

No imports were removed.  The direct declarations for finite reduction and normalized vector
bundle purity are used.  The detailed scalar trace, compact coherence, and transpose declarations
remain dependencies of the fixed-witness intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The quarantined build failure reported a stale bad import of
`Sheaf.Paper.VectorPurityFiniteReduction`; the current module exists and compiles.  The original
single theorem proof required two independently substantial arguments, so they were split into
strictly smaller line-existence and fixed-witness compatibility statements.

## New nodes

`lem-pur-normalized-vector-purity-scalar-line-witness` records the target Tate-line comparison
existence and its normalization.  Its module is
`lean/Sheaf/Paper/NormalizedVectorPurityScalarLineWitness.lean`.

`lem-pur-normalized-vector-purity-scalar-compatibility` records the fixed-witness scalar
compatibility calculation.  Its module is
`lean/Sheaf/Paper/NormalizedVectorPurityScalarCompatibility.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NormalizedVectorPurityScalarCompatibility": "9a258e4083aa93bbb067ad31e8a9fc03a931b617", "Sheaf.Paper.NormalizedVectorPurityScalarLineWitness": "8da7df1af971d35de7e497d9e6d856af8f37c810", "Sheaf.Paper.NormalizedVectorPurityScalarReduction": "ea432286482215d7da9186bbbc260a863a2c65a0"}, "results": {}, "time": "2026-10-28T01:02:41+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
