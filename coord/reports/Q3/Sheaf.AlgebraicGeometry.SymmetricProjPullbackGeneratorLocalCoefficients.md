## What changed

Added two strict intermediate chart statements and imported them into the assigned module:
`normalized_pullback_generator_local_coefficients_q` supplies the local open, first frame,
and coefficient map for `q`; `normalized_pullback_generator_local_coefficients_qprime`
supplies the matching second frame and `q'` equation for the same data. The assigned
parent theorem remains stated unchanged and its proof hole remains open because kernel
checking the dependent `q'` transport exceeded the 60-second per-file limit when the two
intermediate results were paired.

## Proved and sorry left

The two intermediate declarations compile and are intentionally split-off `sorry`s:

- `AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients_q`
  (node `lem-trf-symmetric-proj-pullback-generator-local-coefficients-q`).
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients_qprime`
  (node `lem-trf-symmetric-proj-pullback-generator-local-coefficients-qprime`).

The assigned declaration
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients`
remains a `sorry` (node `lem-trf-symmetric-proj-pullback-generator-local-coefficients`).
No definition contains a `sorry`.

## No longer needed

None. The assigned module's original imports remain needed for its statement, and the
four chart dependencies remain the stated proof dependencies of both split lemmas.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof hid two independent local calculations: the first
pulled quotient equation and the normalized second quotient equation. The strict split
makes those calculations explicit. The parent combination is mathematically immediate,
but Lean's kernel spends over 60 seconds checking the dependent transport in the `q'`
equation when the two independently elaborated local expressions are combined; the
intermediate statements compile individually in under six seconds.

## New nodes

`lem-trf-symmetric-proj-pullback-generator-local-coefficients-q` records the first local
frame and `q` equation. `lem-trf-symmetric-proj-pullback-generator-local-coefficients-qprime`
records the matching second frame and `q'` equation. Both use the existing canonical
symmetric graded algebra, relative Proj functoriality, standard-open, and pulled-chart
normalization declarations.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients": "c28171ec9a77aa331e4e02c5d8608f8eece0d2f7", "Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficientsQ": "396fb46054fa7562679f299ad84b139d90f11a3c", "Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficientsQPrime": "4b067a793bda6e9c64f4545b17767a67c9045a97"}, "results": {}, "time": "2026-10-28T08:28:34+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
