## What changed

Replaced the hole in
`WeilConjectures.PurStrictScalar.finiteOrdinaryBalancing_existsUnique`
with a proof assembling single-module tensor/quotient comparisons into a natural
isomorphism and proving uniqueness. Added two proved private helpers: the scalar
adjunction identifies maps out of scalar extension by their values on `1 tensor x`,
and naturality of its unit identifies the image of those generators under every
module morphism.

Added the proof-only import `Sheaf.Paper.FiniteQuotientModuleBalancing`. Its one
public theorem isolates the existence of the normalized comparison for one finite
quotient module and one exponent. It assumes neither naturality nor uniqueness.
The consuming proof establishes both using the two scalar adjunction units and the
specified tensor formula. Existing definitions, public imports and the unit route
are unchanged. The final
theorem retains all original binders and the same proposition; its large conjunction
is now the body of the transparent abbreviation
`WeilConjectures.PurStrictScalar.compactSupportStrictScalarMateConclusion`.
The abbreviation body is the verbatim original conclusion. This avoids repeated
inspection of the expanded result. Earlier runs reported 22--24 seconds in
end-of-file processing under the profiler label `linting`. Updated
Step 7 of the existing node to
record this argument and its new dependency. Normal transparency checking is
localized to the new proofs and the final theorem statement to keep elaboration
within the per-file budget; the original global options are preserved.

Validation: the component module compiled in the delivery preflight (53.5 seconds).
The final main module, including the conclusion abbreviation, subsequently compiled
in 51.4 seconds with no Lean errors. All profiler/trace settings are removed from
the delivered version. The required delivery preflight verifies that final version.

## Proved and sorry left

This is a decomposition: one original hole is closed using one strictly smaller
new hole. There is no claimed net reduction in the number of holes.

Closed original hole:

- `WeilConjectures.PurStrictScalar.finiteOrdinaryBalancing_existsUnique`
  (node `lem-pur-compact-support-strict-scalar-mate`): naturality, simultaneous
  existence and uniqueness are now proved from single-module existence.

Original holes retained with the same mathematical statements, all attached to
`lem-pur-compact-support-strict-scalar-mate`:

- `WeilConjectures.PurStrictScalar.pulledBasis_existsUnique`.
- `WeilConjectures.PurStrictScalar.proper_biproduct`.
- `WeilConjectures.PurStrictScalar.strictProper_biproduct`.
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate`.

Added hole:

- `WeilConjectures.PurStrictScalar.finiteQuotientModuleBalancing_exists`
  (node `lem-pur-finite-quotient-module-balancing`): tensor/quotient cancellation
  for one module, with its prescribed pure-tensor formula. The docstring and node
  give the complete construction and account for sheafification and the actual
  completed quotient projections.

The assigned module started with five holes and now has four; the new module has
one. No holes were added in definitions or private declarations.

## No longer needed

None. No existing imports, nodes, modules, declarations or unit steps are removed.
The ordinary finite comparison still needs tensor/quotient cancellation; its
naturality and uniqueness no longer require separate assumptions. The unrelated
ordinaryScalarBalancingLevel_exists cannot replace the new component theorem
without additional quotient-adjunction identifications: its input is a completed
module, whereas this comparison accepts an arbitrary finite quotient module.

## Where the brief, the DAG or earlier work was wrong

No statement error found. One compile request stopped before elaboration because
the server lacked the imported artifact
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree.olean`.
A second compile request then stopped on the missing artifact
`WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent.olean`.
No source or tool workaround was attempted. These were transient missing server library
artifacts; the subsequent compile succeeded. They were separate from the
per-file runtime failures, which were addressed in the sandbox.
Step 7 bundled single-module tensor
cancellation with naturality and uniqueness; the latter two are formal consequences
of the normalized scalar adjunction and are now checked in Lean. The four other
original obligations are retained for later work. The new component lemma is true
also for the zero module and empty site objects; the hypotheses guarantee both
quotient exponents are positive. Its inverse uses the tensor/quotient universal
property, without assuming global lifts of arbitrary sheafified sections.

## New nodes

`lem-pur-finite-quotient-module-balancing`, in
`dag/nodes/sec-smooth-purity/lem-pur-finite-quotient-module-balancing.json`, states
only the existence and original pure-tensor formula at one module and exponent.
Its module is `Sheaf.Paper.FiniteQuotientModuleBalancing`. It is a proper part of
Step 7: the existing theorem additionally requires naturality in every module and
uniqueness of that natural comparison, both proved in this delivery. Searches found
Mathlib tensor/quotient algebra but no comparison with these specified sheafified
scalar functors. The definitional presentation change is recorded in
`coord/changes/compact-support-strict-scalar-conclusion.md`. The consumer search
found no other module referring to the final theorem by name. No consumer is adapted.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
