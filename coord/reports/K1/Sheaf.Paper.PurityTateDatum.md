## What changed

Filled the two helper proofs in `Sheaf.Paper.PurityTateDatum`, following their
existing proof docstrings. `twistedFrobeniusSquareOver` uses `Over.w` for the
base-changed morphism and the supplied square equation to verify the four
structure equations. `twistedFrobeniusFiniteClasses` installs the geometric
Frobenius isomorphism instances from `schemeGeometricFrobenius_squares` and uses
Mathlib's composition instances for the twisted structure maps. The arrow
properties are the original hypotheses, since twisting only changes the
structure morphisms.

## Proved and sorry left

Closed 2 of 2 holes, both attached to `def-pur-tate-datum`:

- `WeilConjectures.Purity.twistedFrobeniusSquareOver`.
- `WeilConjectures.Purity.twistedFrobeniusFiniteClasses`.

No holes remain in the item module. No holes or split-off statements were added.
The surrounding derived-category constructions still depend on the library's
existing declarations; this delivery makes no claim to close their dependencies.

## No longer needed

None. All existing imports support the published statements and constructions;
no new import is needed for these elementary helper proofs. The existing node
has no proof dependencies to prune, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

Validation: the complete module compiled in 17.9 seconds. The unused square
parameter in the second proof is eliminated by cases while preserving its name
and type for all consumers; the final delivery reruns the compiler and preflight.

No mathematical discrepancy found in the two assigned helper statements.
Their existing proof docstrings give direct proofs. The first proof uses the
supplied `CommSq` rather than recomputing its equation. The second uses the
existing scheme-geometric-Frobenius theorem. There are no additional domain
hypotheses, changes to definitions, statement changes, or consumer adaptations.

Searches were run through `msearch.py`: LeanFinder for twisted square and
composition properties, Loogle for `Scheme.Hom.IsOver`, and grep for composition
instances. The relevant existing Mathlib interfaces are `Over.w`,
`locallyOfFiniteType_comp`, and `quasiCompact_comp`. Both arguments are valid
also in relative dimension zero and for empty schemes; neither makes a
nonemptiness assumption or divides by a dimension or coefficient exponent.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
