## What changed

Proved `AlgebraicGeometry.Scheme.integralResidueFiniteConstants` without changing its
statement. All helper declarations are private and proved, inside the assigned module.
The proof normalizes the finite coefficient map on quotient representatives, compares
ordinary associated-module constant functors, and localizes their degreewise isomorphism.
Derived scalar extension along the normalized ring isomorphism is identified with exact
restriction along its inverse by uniqueness of left adjoints. The canonical localization
representative in `integralResidueFiniteModel` is removed using its supplied isomorphism.

Proof-only imports expose existing proved helpers from the finite reduction,
constant-module constructibility, finite coefficient realization and residue-lisse modules.
The three existing public imports are preserved. General ring-sheaf comparisons are
proved with abstract coefficient parameters and then specialized, so elaboration does
not repeatedly unfold the DVR coefficient constructions. The item's DAG proof and dependencies
are updated to match this argument. No other existing module is changed.

Validation: the final module compiled through `lcompile.py` in 36.4 seconds with no
errors or warnings. Its theorem signature and all three public imports match the
repository source verbatim. All delivered Lean lines are at most 100 characters;
there are zero textual holes and no profiling options.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.integralResidueFiniteConstants`
(node `lem-weil-pbc-integral-residue-finite-constants`), one original hole.
Added: none. Remaining in the delivered module: none. No decomposition or new node.

## No longer needed

No public import is removed and no module is withdrawn. The original four declared
proof dependencies remain necessary for their coefficient definitions, normalizations
and exact functor APIs. The geometric theorem `residue_lisse_perfect_lift` itself is not
used: the same module supplies `residueLisseDerivedConstant` and the normalized
`residueLisseConstantComparison`. No further perfect-lifting, stratum, chart, covering,
boundedness or finite-projectivity lemma is needed for this global comparison.

## Where the brief, the DAG or earlier work was wrong

No false statement or necessary interface repair was found. The existing two-step plan
can be realized from proved infrastructure; the obligation does not require another
split. The proof applies to arbitrary complexes, including zero and unbounded complexes,
and uses no assumption that the scheme is nonempty. Ring-sheaf commutativity is forgotten
explicitly in the scalar square, rather than identifying the two coefficient categories.
The blueprint unit route and all target signatures are preserved.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
