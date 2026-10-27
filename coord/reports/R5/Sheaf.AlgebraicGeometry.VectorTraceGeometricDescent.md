## What changed

The base-change equation is reduced to the strictly local two-frame exchange
calculation in `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal`.
The parent proof constructs the actual exchange isomorphism, independent frame
covers on S and T, and their pointwise common refinement. The local calculation
is applied to the defining normalization of the two existing integrations.
A proved private helper uses singleFunctor full faithfulness, the local Hom
correspondence and jointly faithful sheaf inverse images to descend equality.
The current source's swap, projection and other proved clauses are preserved.
No existing public signature or definition is changed. Local irreducibility
attributes prevent expensive unfolding of the sum-integration and coefficient
constructions while checking later statements; no public reducibility is changed.
The existing proved private generic projection helper is also a high-priority local
instance, avoiding expensive specialized vector-geometry matching in the inverse
projection term. Exact-derived functor definitions are locally irreducible during
the later cover/concentration proofs to prevent expansion of derived constructions.
The swap proof likewise passes its
actual target integration and normalization equation explicitly to the local
calculation, and supplies the exchange component isomorphism explicitly.
These are proof-only adaptations. The existing concentration proof is preserved verbatim.
The complete parent module compiled successfully in 35.7 seconds before final cleanup.
The local module also compiled successfully. Delivery runs the final checks again.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.vectorBundleIntegration_baseChange` by a
strict decomposition. Added one hole,
`AlgebraicGeometry.Etale.vectorIntegration_baseChange_local` (node
`lem-pur-vector-integration-base-change-local`), whose conclusion is only a
restriction equation on W for arbitrary arrows prescribed on two single frames.
The unchanged original `AlgebraicGeometry.Etale.vectorBundleIntegration_directSum`
(node `lem-pur-vector-trace-geometric-descent`) remains sorry. The current source
has two original holes; one is reduced to one local hole, so this is decomposition
with net zero holes closed, not a sorry-free proof. No other holes are added.

## No longer needed

No modules are withdrawn, and no existing imports are removed. All existing
statement imports are preserved. The geometric relative-Spec, symmetric-algebra,
affine counit, twist and exchange dependencies remain needed in the existing
geometry and new local calculation. The direct-sum proof dependencies remain
needed by its unchanged open proof plan. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing dependency statements give the constituent affine trace and exchange
identities, but do not state their two-frame vector-bundle base-change calculation.
That glue is now isolated with the exact exchange and coefficient comparisons and
the two local input equations. It is strictly a local step of the existing Step 3,
not the global equation renamed. The parent records the actual Lean cover and
full-faithfulness argument. Empty bases, empty refinement opens, rank zero and the
zero coefficient ring require no extra hypothesis and are included.

## New nodes

`lem-pur-vector-integration-base-change-local` records the exchange calculation on
a common refinement of one source frame open and one pullback-bundle frame open.
Its source is paragraph 2 of the current vector-bundle purity proof, corresponding
to geometric-descent Step 3. Its module imports only the existing geometry/charts
interface. Its docstring and node give the generator identification, exchange
pasting, Tate composition, affine base change, frame invariance, and constant-unit
cancellation argument. No change record is needed: all public statements and
definitions of existing modules are preserved.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
