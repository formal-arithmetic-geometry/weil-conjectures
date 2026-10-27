## What changed

Proved `WeilConjectures.PurScalarProjection.openProjection_existsUnique`.
A proved private helper transports intrinsic DVR open completeness to the actual
completed-ring open extension. The completion reflector then supplies the unique
map with exactly the required unit equation. Public signatures and definitions
are unchanged. The item node records this argument and its existing dependencies.

The canonical DVR coefficient and open models are supplied by the proved private
constructors in `OpenQuotientKoszulCompleteness`, imported with `import all`.
The intrinsic completeness criterion, its quasi-compact open transport and the
ringed identification are existing declared dependencies, not new split-offs.
They have precisely the arbitrary-scheme hypotheses needed here, including the
empty open; no finite-type or prime-invertibility hypothesis is added.

## Proved and sorry left

Closed one of the four starting holes:
`WeilConjectures.PurScalarProjection.openProjection_existsUnique`.
Added no holes and split off no statements.

The three remaining holes are unchanged:
- `WeilConjectures.PurScalarProjection.realization_existsUnique`
- `WeilConjectures.PurScalarProjection.native_scalar_identification`
- `WeilConjectures.PurScalarProjection.gamma_identification`

Validation: the remote single-file compile succeeded in 51.0 seconds.
The delivery tool runs the final compilation and preflight checks.

## No longer needed

No modules, imports or nodes are withdrawn. The completed open tensor system
realization is not needed for the newly proved unique-extension theorem: target
completeness and the completion-unit Hom bijection suffice. Its stronger finite
system normalization remains needed by the three open comparison holes, so its
DAG dependency is retained. The unit's proof route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or tooling defect found. The original Step 6 planned a stronger
finite-system identification than this named unique-extension theorem needs.
The updated node distinguishes the proved component from that remaining plan.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
