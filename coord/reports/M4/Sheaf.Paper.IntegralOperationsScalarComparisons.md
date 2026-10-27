## What changed

Proved `WeilConjectures.scalarCompletion_existsUnique` in
`Sheaf.Paper.IntegralOperationsScalarComparisons` by applying the fully proved
`WeilConjectures.normalizedIntegralScalarCompletion` in the new module
`Sheaf.Paper.NormalizedIntegralScalarCompletion`. The proof transports the existing
ordinary scalar model through its universal derived comparison, composes with
`completedScalarComparison`, and checks the prescribed quotient-completion square
using `integralScalarCompletionChain_model`. The finite-free comparison proves
invertibility after converting intrinsic completeness to the legacy predicate.
Localization on good complexes and cancellation of their representative comparisons
prove uniqueness.

The item privately imports the new proved module and applies its theorem directly
by definitional equality of the normalization predicate. That module uses proof-only
`import all` declarations for `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
and `Sheaf.Paper.IntegralScalarExtensionConstructible` to use their proved model
APIs, plus the intrinsic/legacy completeness comparison. Updated the main
scalar-operations node and the existing normalized scalar-completion node; the
latter is attached to the new helper theorem. No new DAG node is needed. All
existing signatures, public imports, definitions, and the unit route are preserved.

Explicit typed wrappers for the ordinary counit, completed functor and
representative comparison confine unfolding to the model identifications. The
complete original module still took 71.5 seconds, so the proved normalization
argument was extracted into its own module. Profiling then identified about
40 seconds in the existing local registration of `IntegralOnSlice.hasDerived`.
Making `IntegralOnSlice.ring` locally irreducible only during that registration,
then restoring its usual semireducibility, avoids this expansion. This changes
no shared definition or exported attribute. The delivered files typechecked in
45.8 seconds for the new module and 54.8 seconds for the item module; profiling
options were removed.

Searches with the prescribed LeanFinder, Loogle and grep interfaces found the
localization extensionality API; repository searches found the existing normalized
scalar-model transport and finite-free comparison.

The argument applies to arbitrary unbounded complete inputs and arbitrary schemes;
it introduces no constructibility or geometric finiteness assumption. The identity
embedding, zero complex and empty scheme are covered by the same normalization and
localization argument.

## Proved and sorry left

Closed 1 of the item's original 8 holes; the new helper theorem is fully proved:
`WeilConjectures.scalarCompletion_existsUnique`
(`lem-weil-normalized-scalar-completion`, also attached to
`lem-pur-integral-operations-scalar-extension`). Added 0 holes; split off 0 unresolved statements. The new helper module has zero
holes.

The seven remaining holes, left unchanged, all belong to
`lem-pur-integral-operations-scalar-extension`:

- `WeilConjectures.scalarPullbackLevel_existsUnique`
- `WeilConjectures.scalarPullbackTower_existsUnique`
- `WeilConjectures.scalarTensorLevel_existsUnique`
- `WeilConjectures.scalarTensorTower_existsUnique`
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`
- `WeilConjectures.scalarTensorOrdinary_existsUnique`
- `WeilConjectures.scalarOperationsOrdinary_tower`

## No longer needed

No Lean imports or modules were removed. The completion proof no longer directly
uses `lem-pc-kflat-resolution` or
`lem-weil-integral-scalar-extension-well-defined`; their roles are supplied by the
existing normalized comparison and good-localization theorems. These two direct
proof dependencies were removed from `lem-weil-normalized-scalar-completion`.
They remain relevant to other declarations, so no global module pruning is claimed.
The main node retains the dependencies of the seven unfinished clauses.

## Where the brief, the DAG or earlier work was wrong

The normalized completion node previously described direct resolution descent.
The existing ordinary scalar-model isomorphism, universal derived comparison and
finite-free normalized comparison already supply that construction and its
invertibility. Reusing them leaves only the explicit counit square and localization
uniqueness to prove here.

The existing auxiliary nodes
`lem-pur-integral-operations-scalar-extension-pullback-clause` and
`lem-pur-integral-operations-scalar-extension-hom-clause` name component declarations
that are absent from the current item source. This delivery does not use or alter
those stale attachments; the original three-clause tower theorem remains unchanged.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
