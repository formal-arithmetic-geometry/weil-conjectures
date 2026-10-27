## What changed

Replaced the hole in `WeilConjectures.IntegralSystemRealization.ordinaryOpenReduction_isIso`
by an ordinary adjunction argument. Integral open extension is fully faithful. The
finite quotient of an extended integral module lies in the finite open essential
image. Evaluation of the system counit then proves that counit invertible on the
reduced extended module. Expanding the specified inverse mate expresses it as a
composite of isomorphisms.

Added proof imports of `OrdinaryFiniteQuotientOpenSupport`,
`OrdinaryOpenFiniteEvaluation`, `ProEtaleOpenSlicePresentation`, and a private proof
import of the existing slice-unit helper from `OpenImmersionTensorPiece`. The new
finite-support module publicly imports only completed coefficient data; its
tensor machinery is a proof import. Existing
public imports, definitions, theorem signatures and docstrings stay unchanged.
Updated the item's node proof and dependencies to describe this route.

All three modules compiled successfully through `lcompile.py`. The first clean
delivery compile of finite support exceeded 60 seconds, despite a subsequent
profile showing under one second each for elaboration and type checking. The
revised support module uses the ordinary constant-ring comparison directly,
removes its strict-tower import, and locally hides the large completed coefficient
constructions from unification. The main proof
uses local irreducibility attributes on the large sequence-ring definitions to
avoid expanding their limit construction during joint reflection of isomorphisms.
With these attributes the reflection helper type-checks in 172 ms; the final main
module compile completed in 3.9 s. Temporary profiler options were removed before
delivery. The two auxiliary modules also compiled below the per-file limit.

## Proved and sorry left

Closed the item's one hole:
`WeilConjectures.IntegralSystemRealization.ordinaryOpenReduction_isIso`.
Also proved the new auxiliary theorem
`WeilConjectures.IntegralSystemRealization.ordinaryFiniteQuotientOpenSupport`
(node `lem-sf-ordinary-finite-quotient-open-support`) from the existing coefficient
square, scalar-restriction comparison, adjunction uniqueness and slice presentation.
Its module contains zero holes and has compiled successfully with the project compiler.

Added one hole:
`WeilConjectures.IntegralSystemRealization.ordinaryOpenFiniteEvaluation`
(node `lem-sf-ordinary-open-finite-evaluation`). This asserts compatibility of ordinary
system open extension, finite evaluation and their counits. It contains no integral
reduction, completed module or OrdinaryLimitModel. It is one strict geometric step
of the original argument, with a full proof in words in its docstring. The empty
and identity opens, zero modules and the first positive quotient have the same
slice/direct-sum formulas. No data definition is selected from this theorem.

The delivery is a decomposition: one existing hole closed, one lower hole added;
net zero holes closed. The item's module itself has zero remaining holes.

## No longer needed

No original imports or modules are removed and no nodes are withdrawn. The
development-only strict-tower import in the new support module was replaced by
`ProEtaleConstantRingOperations`; no strict or derived tower machinery is needed. All three
original declared dependencies remain needed for definitions and reduction
comparison. The explicit quotient-generator identification using `a.projections`
is unnecessary for invertibility: `a.reductionPull` is already an isomorphism,
and full faithfulness plus open support make the mate invertible. This avoids
adding a separate normalization lemma or deriving it from the projection equations.
No unit statement or realized unit proof step is bypassed. Blueprint searches for
"open evaluation" and "finite quotient open" found no duplicate blueprint statements.

## Where the brief, the DAG or earlier work was wrong

The planned section-normalization calculation is sufficient but stronger than
needed for this invertibility assertion. The existing declarations do not directly
supply ordinary open/counit evaluation for the actual coefficient sequence inverse
image. The older semilinear slice models describe this evaluation, but transporting
them to the specified actual inverse image and its counit is a separate geometric
step. That step, rather than the original quotient/open mate assertion, is the
single remaining hole. No statement is disputed or weakened.

## New nodes

`lem-sf-ordinary-finite-quotient-open-support`, in
`Sheaf.SixFunctors.OrdinaryFiniteQuotientOpenSupport`, proves finite quotient support
using the commuting restriction-of-scalars square and uniqueness of composite left
adjoints, then applies the counit criterion for fully faithful left adjoints.

`lem-sf-ordinary-open-finite-evaluation`, in
`Sheaf.SixFunctors.OrdinaryOpenFiniteEvaluation`, isolates evaluation of ordinary
system open extension and its counit. Its source is the ordinary open-factor
argument in fix-prop-coherence and Stacks 03DI, 03DJ, 0941; its proof describes
slice extension, vertical sheafification and counit normalization. It is independent
of reconstruction and integral scalar reduction. No change record is needed:
only the assigned existing module and its own node, and new modules/nodes, change.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
