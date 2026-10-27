## What changed

Reused the proved canonical-model theorem
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange`
in the small-model adapter
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel`.
The explicit Spec-of-colimit-isomorphism transport and the structural/residue equations
remain. The concluding canonical-model application replaces the repeated projective-line
pullback, localization and strict-local additive-equivalence assembly.

The canonical theorem is imported privately. Its existing signature, public imports,
proof and source-library module are untouched. The assigned small-model theorem's
complete signature and all five public imports are byte-identical to the baseline.
Its proof docstring and DAG proof now describe the adapter and the reused assembly.
The DAG retains all four mathematical dependencies: the canonical implementation
uses the same pullback, localization and strict-local exchange results. There is no
self-edge, new node, definition change, statement change or unit-route change.

## Proved and sorry left

Actual baseline: zero textual holes. After this delivery: zero textual holes.
Holes closed: none (0 of 0); holes added: none; split off: none.
The small-model theorem remains fully proved. This is reuse of a completed proof,
not a new hole closure or a decomposition. No obligation is handed on.

The revised module compiled without warnings in 6.4 seconds through lcompile.py.
The byte-identical consumer
`Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange`
then compiled against it without warnings in 20.9 seconds. The baseline item also
compiled without warnings (21.1 seconds). The unchanged consumer was copied only
for that check and is not included in the delivery. An explicit `#print axioms` check also compiled without warnings (5.6 seconds)
and reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`. The delivery tool additionally compiles the item with its declaration/axiom
probe before pushing.

Checked byte-for-byte preservation of the complete theorem signature and public
imports, the 100-character line bound, and equality of proof_deps with the union
of proof-step uses. The import-direction check permits the canonical theorem import.

## No longer needed

Removed the two direct private imports
`WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization`
and `WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange`.
The existing canonical projective-line theorem now packages those two applications.
Their declarations and proofs remain unchanged in the source library, and the
corresponding DAG dependencies remain needed through that theorem. The projective-space
pullback dependency is likewise still used there. No node or module is globally pruned.
All public statement imports and the small/full structural-map comparison import stay.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief describes an unresolved obligation and five prior split-offs, but
the current assigned module already has a complete proof. Its restore and name-collision
repairs landed previously. There is no current item return or rework row. The historical
retirement inventory marks the two interfaces DIFFERENT: the small-model theorem takes
`strictHenselizationScheme`, whereas the adopted one takes `strictLocalization`.
The small-model caller still uses this adapter, so withdrawing it would break that
interface; retaining the adapter and reusing the adopted theorem is the shorter route.

LeanFinder, Loogle and Mathlib grep were run through msearch.py. They returned no exact
Mathlib replacement. Repository search located the complete canonical theorem and the
existing structural-map comparison. The current blueprint unit and the local Stacks
source were read, including higher-direct-image restriction complexes, exact closed-point
sections, and the final projective-line stalk calculation. No new mathematical result
or assumption is introduced. In degree zero, for zero coefficients, arbitrary cartesian
models and inseparable extensions of separably closed fields, the same explicit transport
and existing canonical theorem apply without adding hypotheses.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
