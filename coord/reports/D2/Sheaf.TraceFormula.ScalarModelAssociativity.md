## What changed

Replaced the whole-proof `sorry` in
`WeilConjectures.scalarModelAssociativity` by a proof from the strict iterated-route
calculation, the existing scalar realization normalization, the existing ordinary
associator normalization, and localization on good complexes. The displayed theorem
statement and all existing public imports are unchanged.

The proof packages both routes as natural transformations. On a good representative
it chooses the simultaneous reduction presentation supplied by `SE.reductionModel`,
and uses the direct model `bEF.normalization` to obtain its generator-normalized tower
identification. The endpoint composite is invertible because its composite with
`bEF.realization` is the prescribed scalar representative isomorphism. The strict
iterated calculation computes the other path. The ordinary associator counit equation
and the defining completion-comparison equation give the direct path. Cancellation
and localization natural-transformation extensionality finish the ambient statement.
No completion comparison is inverted.

Validation: both modules compiled through `lcompile.py --all`; after adding local
irreducibility attributes, the profiled compiles took 49.3 seconds for the strict
calculation and 54.2 seconds for the main module. The only warnings concerned the
temporary profiler options, which were removed before delivery. The delivery tool
will compile the final sources again and run its declaration/axiom and record checks.

Added the proof-only imports of the new strict-calculation module and
`import all Sheaf.Paper.IntegralOperationsWellDefined` to use the existing localization
theorem. Updated the item's proof plan and added the new node and module. Local irreducibility attributes prevent elaboration from
unfolding the large chosen scalar functors and system models; they do not change
any shared definition or public interface.

## Proved and sorry left

This is a decomposition, with one upper hole closed and one strictly smaller hole
added; net holes closed: zero. It is not a complete proof without remaining
obligations.

- Closed the original hole in `WeilConjectures.scalarModelAssociativity`
  (`lem-trf-scalar-model-associativity`). Its proof from the named strict calculation
  and existing declarations is complete.
- Added one hole: `WeilConjectures.scalarModelIteratedStrictCalculation`
  (`lem-trf-scalar-model-iterated-strict-calculation`). This computes just the iterated
  path on a fixed simultaneous strict quotient presentation. It has only the two
  iterated scalar models, no direct E-to-F scalar realization, and no ordinary derived
  associator. Its conclusion is a formula in the universal ordinary scalar counits,
  the localized sheaf associator and the actual strict quotient augmentation.
- No other `sorry` occurs in either delivered module; none is added to a definition.

## No longer needed

No existing public import was removed, no module is withdrawn, and no global pruning
is claimed. The original strict quotient and cone-counit work remains needed in the
new strict-calculation node. The parent now uses that node instead of carrying the
K-flat scalar-change, quotient descent and cone-counit calculation in its own proof.
`primitiveQuotientScalarTriple` was also checked: it proves finite-level tensor
associations and imposes residue-unit hypotheses, so it does not supply the ambient
whole-system counit calculation required here. `primitiveQuotientRealizations_unique`
compares two already normalized primitive models, rather than computing the iterated
route through the middle reduction counit.

The separate general ordinary-module derived-change-of-rings node
`lem-pur-derived-change-of-rings` is not directly used: the existing specified
`completedScalarCounit` and its normalization already supply that API.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original DAG plan combines a
strict whole-system calculation with the simpler direct-model and derived-localization
steps. The latter steps are now implemented; the strict calculation remains explicit.
The endpoint universal system scalar counit need not itself be inverted before taking
the limit: the direct model normalization proves invertibility of the entire endpoint
composite used for cancellation. This avoids asserting a stronger unsupported
invertibility statement.

## New nodes

`lem-trf-scalar-model-iterated-strict-calculation`, in
`lean/Sheaf/TraceFormula/ScalarModelIteratedStrictCalculation.lean`, isolates the strict
part of parent steps 1--3. Its source and complete proof in words are in its docstring
and DAG node. Its tensor-generator hypothesis fixes the endpoint tower isomorphism
without assuming the original associativity equation. The original proof still supplies
the direct-model normalization, the representative ordinary associator equation,
completion-comparison descent, cancellation and transport to all derived objects.
No shared interface changed, so there is no change record or consumer adaptation.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
