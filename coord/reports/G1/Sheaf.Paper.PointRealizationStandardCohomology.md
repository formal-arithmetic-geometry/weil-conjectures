## What changed

Filled `WeilConjectures.pointExactDerivedComparison_existsUnique` using the existing
exact-derived functor, its bound-preservation lemmas, and its prescribed good-truncation
isomorphisms. The counit/unit equations follow from `liftTruncLE_ι` and
`π_descTruncGE`; uniqueness follows by fixing all three data fields and proof irrelevance.

Filled `WeilConjectures.pointRealizationIntegralNormalization_existsUnique` by assembling
the recorded rational object equality, size-descent counit, lift/down comparison and
coefficient-down rational comparison. The pure-tensor formula at scalar one proves
naturality of the restriction along integral localization. The resulting components are
exactly `pointRationalNormalization`; pointwise equality proves uniqueness.

All existing declaration signatures, definitions, visibility and docstrings are preserved.
The two completed proofs compiled through `lcompile.py` in 25.9 seconds.
No data is selected from a new existence assumption. The existing uniquely normalized
interfaces of `FiniteCoefficientPoint` are used as stated.

## Proved and sorry left

Original hole count: four. Closed two holes, added zero, split off zero:

- `WeilConjectures.pointExactDerivedComparison_existsUnique`.
- `WeilConjectures.pointRealizationIntegralNormalization_existsUnique`.

Two existing named theorem holes remain, both attached to
`lem-a1-point-realization-standard-cohomology`:

- `WeilConjectures.pointRealizationStageNormalization_existsUnique`.
- `WeilConjectures.pointRealizationStandardCohomology`.

The latter still requires the finite/scalar normalized comparisons and their common-stage
descent. This is a partial delivery closing independent existing holes, not a claim that
the final point-cohomology system is established without its existing assumptions.

## No longer needed

No mathematical node or module is withdrawn. The node's eight-step plan and dependencies
remain for its two open declarations. No new dependency, split-off theorem or node is added.

The private imports supporting the remaining proof plan are retained. The two closed
holes need no additional imports; exact-derived-functor infrastructure is already
available through the statement imports. Their shorter assembly does not eliminate
any dependency needed by the module's remaining final theorem.

## Where the brief, the DAG or earlier work was wrong

The first hole already has the exact functors and good-truncation maps in the adopted
source library; only their assembly and uniqueness were missing. The integral
normalization is likewise an assembly of the recorded normalized maps, with naturality
on integral arrows obtained directly from the rational fibre specification at scalar one.

The item's source existed and was read and copied at session start. It temporarily
disappeared from the shared checkout and was restored during the session. Comparing
the restored source against the sandbox confirms that only the two theorem proof
bodies differ. The full original interface and unproved declarations are preserved.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
