## What changed

Filled `WeilConjectures.commonStageTensorAssociator_naturality` in
`Sheaf.Paper.CommonStageTensorLineCoherenceNaturality`, preserving its statement.
Added a private proof import of `Sheaf.Paper.IntegralSystemReductionFullyFaithful`.
The proved private helpers establish naturality through coherent reduction, extend it
by induction on the three rational Hom tensor products, and cancel the prescribed
common-stage comparisons at one finite coefficient field. Updated the existing node's
proof to match these calculations.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.commonStageTensorAssociator_naturality`
(node `lem-pur-common-stage-tensor-associator-natural`).
No holes added; no `sorry` remains in the delivered module. All private helpers have
complete proofs. Existing imported statements are used as authorized stage-3 dependencies.

## No longer needed

No existing imports removed. The direct proof dependency
`lem-coef-completed-tensor-scalar-linearity` (module
`Sheaf.Paper.CompletedTensorScalarLinearity`) is unnecessary for this proof: the
rational tensor's existing bilinear-map specification supplies exactly the linearity
and pure-tensor formula needed for the three inductions. Its dependency was removed
from this node; no assertion is made that its module is globally unused.
All other declared dependencies remain used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned argument works with the existing declarations. The common-stage tensor
and constraints are specified separately, so ordinary monoidal naturality cannot be
applied directly to the common-stage category. Explicit representative substitution
and the integral-to-rational calculation bridge that interface without introducing
another unproved naturality statement. The final generic application specifies both
the named finite-stage type and its cached category instance; this avoids an expensive
conversion between definitionally equal category presentations. No profiling options or
diagnostic code remain. No statement or definition repair was needed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
