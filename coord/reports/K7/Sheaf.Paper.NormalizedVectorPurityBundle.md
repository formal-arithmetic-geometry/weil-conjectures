## What changed

Filled `WeilConjectures.PurityFiniteSetting.vectorBundleNormalized` in
`Sheaf.Paper.NormalizedVectorPurityBundle`, keeping its statement unchanged.
Two proved private categorical helpers conjugate the coefficient-first integration mate
and assemble its normalized natural family, restricted uniqueness, and coefficient-unit
orientation. Two further proved private helpers specialize first to abstract étale
coefficients and then to finite module coefficients. The finite specialization retains
the trace's native `ordinaryFiniteUnit` target, avoiding repeated kernel reduction of
constant-sheaf and tensor-unit presentations. Added a private proof import of
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit` for the existing
projection right-unit equation and the finite-unit comparison. Updated the item's node
proof to describe the implementation.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.PurityFiniteSetting.vectorBundleNormalized`
(node `lem-pur-normalized-vector-purity-bundle`). Added zero holes; zero remain in
the delivered module. The proof uses the established `vectorIntegrationMate_isIso`
for all unbounded inputs; its transitive dependencies remain the work of their items.

## No longer needed

None. Both existing imports remain used, and the declared dependency
`lem-amb-vector-integration-mate` remains used. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The planned generic normalization construction
was not already stated as a theorem: it is now a proved private helper in this module.
The conjugation uses the actual derived signed braiding and the published projection.
The generic argument applies to the zero ring, empty base, and rank zero without any
nontriviality or positive-rank assumption; it uses only invertibility already supplied
by the integration-mate theorem. No definition, public signature, exported attribute, or public
import changed. Local transparency and instance priorities affect only this proof file.

Validation: the final source compiled cleanly in 26.1 seconds after removing profiling
settings. The public declaration signature is byte-for-byte unchanged, and the module
contains zero `sorry` tokens. Delivery runs the remaining mechanical checks.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
