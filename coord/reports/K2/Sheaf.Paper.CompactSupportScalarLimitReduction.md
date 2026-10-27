## What changed

Only `Sheaf.Paper.CompactSupportScalarLimitReduction` and its existing proof-route
node `lem-pur-compact-support-scalar-limit-reduction` change. No statement,
definition, public import, instance or attribute changes.

`scalarRoosComparison_existsUnique` transports the universal derived-limit unit
along the ordinary termwise-limit comparison, then uses the existing Roos
derivation and uniqueness of right derived functors. An arbitrary competing
normalized comparison descends through localization and agrees by right-derived
extensionality. This proves the prescribed normalization on every tower complex,
including uniqueness of the entire natural isomorphism.

The three new imports are proof-only: `StrictRoosDerivedLimitComparison` (private
ordinary-limit comparison), `StrictRoosDerivation`, and `DerivedExactSquareCoherence`
(private canonical derived unit and its universal property). Their existing DAG
nodes are recorded in Step 3. These imports add zero project modules to the
existing import closure. No new nodes or modules are introduced.

## Proved and sorry left

Closed one of the original seven named theorem holes, with no holes added:
`WeilConjectures.PurStrictScalar.scalarRoosComparison_existsUnique`.

The following six original named theorem holes remain unchanged, all attached
to `lem-pur-compact-support-scalar-limit-reduction`:

- `WeilConjectures.PurStrictScalar.scalarLimitTensor_exact`.
- `WeilConjectures.PurStrictScalar.scalarCompletion_existsUnique`.
- `WeilConjectures.PurStrictScalar.scalarLimitRestriction_exact`.
- `WeilConjectures.PurStrictScalar.scalarRoosNormalization`.
- `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization`.
- `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`.

This is a partial proof delivery, not a decomposition: zero split-off statements.
Validation: the complete module compiled cleanly through `lcompile.py` in 56.7 s,
with exit code 0, no warnings and no debugging options. All three proof imports
passed the import-cycle check; the node proof-dependency union matches its steps.
The required delivery command runs the final compile and preflight checks.

## No longer needed

None. No original imports, nodes, modules or unit steps are removed. The remaining
holes still need the recorded geometric, exactness and strict-normalization route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition repair was required. Step 3 previously
omitted the existing universal Roos-derivation and ordinary-limit comparison
interfaces used here; it now records them. The unit route is preserved.

For continuation, the completion comparison can be constructed by reflecting
exactness of completed scalar extension through the underlying-sheaf functor,
using `scalarCompletionOrdinary` and `baseTensor_exact`; localize its fixed
ordinary balancing after identifying the exact derived counit. That argument
was prototyped but is not part of this delivery: its combined elaboration cost
with the existing file still needs work. Its original named hole is unchanged.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
