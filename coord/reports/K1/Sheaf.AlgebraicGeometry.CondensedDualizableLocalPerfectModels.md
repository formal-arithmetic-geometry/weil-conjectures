## What changed

Preserved both public theorem statements and all public imports of
`Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels`.

`condensed_dualizable_stable` now applies the existing source-library zero,
isomorphism, shift and distinguished-cone dualizability API. The proof does not
need a local model, a finite-component hypothesis or projectivity of the unit.

`condensed_dualizable_iff_local_perfect` now has both directions written out.
Perfect scalar realizations are dualizable after passing to the existing
w-contractible affine basis, and dualizability descends through the given cover.
For the forward direction, affine neighborhoods inherit finite component sets
from their containing open neighborhoods. Their model covers are composed with
the point-indexed Zariski cover, with the actual derived pullback comparisons.

Added `Sheaf.AlgebraicGeometry.CondensedAffineLocalPerfectModels`. Its forward
affine theorem assembles the existing irreducible generic-model and finite
closed-lift statements: use minimal-prime quotients, w-contractible faithfully
flat ind-etale extensions, a geometric generic point, and the retained
ClosedLift algebra map. The canonical affine isomorphism transports the
resulting cover back to an arbitrary affine scheme. All auxiliary arguments
are private proved theorems. No source-library declaration was edited.

Validation: both modules compiled together against the published library.
The delivery tool repeats compilation and runs its preflight and axiom probe.

Updated the parent node's proof, proof dependencies, proof origin and obsolete
tool-use entries to describe the actual argument. Added nodes for the affine
assembly and the already proved generic stability API.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.ProEtale.condensed_dualizable_stable`.
- `AlgebraicGeometry.ProEtale.condensed_dualizable_iff_local_perfect`.

Added no holes. The new theorem
`AlgebraicGeometry.ProEtale.condensed_affine_dualizable_local_perfect` and all
private helpers have complete proofs. There are zero `sorry` tokens in either
delivered Lean module. The forward implication uses the existing unfinished
`AlgebraicGeometry.ProEtale.condensed_irreducible_generic_scalar_model`
(node `lem-zl-condensed-irreducible-generic-scalar-model`); its preexisting hole
is not changed or duplicated. Consequently these are proofs from the stated
dependencies, rather than a claim that the entire transitive axiom closure has
already been completed.

## No longer needed

Removed these direct private imports from the item module:

- `WeilConjectures.RingTheory.ProEtale.WContractible`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `WeilConjectures.RingTheory.ProEtale.ClosedLiftMap`.
- `WeilConjectures.RingTheory.ProEtale.ClosedLift`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`.
- `Sheaf.RingTheory.IndEtaleStability`.
- `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity`.
- `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation`.
- `Sheaf.AlgebraicGeometry.GenericFiberComponentsSection`.
- `Sheaf.RingTheory.ProEtale.HenselianClosedLift`.

The reduced-induced-closed-subscheme route
(`lem-weil-pbc-reduced-induced-closed-subscheme`) is not used: minimal-prime
quotient spectra supply the required irreducible closed cover directly.
The parent no longer directly needs
`lem-sc-irreducible-components-cover`,
`lem-weil-pbc-source-wcontractible-extension`,
`def-weil-geometric-point`, `def-weil-algebraic-closure`,
`lem-zl-condensed-irreducible-generic-scalar-model`, or
`lem-zl-condensed-finite-closed-model-lifts`; their necessary mathematical work
is recorded under the new affine assembly node instead.

Removed the parent's obsolete tool-use entries
`lem-weil-pbc-source-wcontractible-extension`,
`lem-weil-pbc-reduced-induced-closed-subscheme`,
`lem-exc-closed-lift-filtered`, `lem-exc-closed-lift-reduction`, and
`lem-weil-pbc-ind-etale-stability`. The weakly contractible basis entry is kept.
The extension and closed-lift work remains necessary transitively in the
affine assembly and its existing dependencies. Likewise most removed direct
imports remain transitive dependencies of the generic-model or lift modules.
No module is withdrawn, and no declaration in the adopted source tree is
removed. The pruning claim is the unused reduced-induced route and redundant
direct dependencies, not wholesale deletion of those transitive modules.

## Where the brief, the DAG or earlier work was wrong

The stability clause has a much shorter route than proving it through local
scalar models: the generic derived shift and cone lemmas are already proved.
No change to either mathematical statement is required.

The affine argument must keep the separate scalar complex for each component;
no common scalar model or global amplitude bound is asserted. An affine open
inside a finite-component neighborhood needs a topological finiteness argument;
this is supplied explicitly using closures of component images under an open
embedding. Empty schemes use empty covers, and quotient spectra of minimal
primes are domains even when the original affine ring is nonreduced. The
reverse implication works without the finite-component hypothesis.

## New nodes

`lem-zl-condensed-affine-local-perfect-models`, attached to the new affine
module and theorem, records the affine forward part of HRS Theorem 4.13. Its
proof is the prescribed generic-model and closed-lift route followed by
transport through the canonical affine isomorphism. It adds no postponed
statement and does not bypass the containing blueprint unit's route.

`lem-zl-derived-dualizable-stability` attaches the already proved generic
source-library shift and cone stability theorems in
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit`.
It adds no Lean declaration and no module. This makes the actual direct
stability dependency explicit in the DAG.

No change record is required: existing signatures, definitions, visibility and
public imports are unchanged; the additions are new node statements and
proved private helpers.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
