## What changed

Proved `AlgebraicGeometry.ProEtale.etale_proEtale_exceptional_transport` without changing its
signature or its three domain/image definitions. The proof constructs functorial etale origins,
uses the existing compactification comparison, transports the given ordinary adjunction's
counit, and proves that the resulting Hom map is bijective by identifying it with a composite
of equivalences.

Added `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison` with the proved theorem
`AlgebraicGeometry.ProEtale.exceptionalTransport_constructible_comparison`. It compares the
intrinsic fixed-module constructibility predicate with the source finite-model predicate,
including empty schemes, then uses the existing bounded-derived reconstruction theorem.
The item node now describes the actual six-step proof and its dependencies.

Validation: two delivery dry runs compiled both modules and passed preflight (CODEX). The existing theorem signature is byte-for-byte unchanged, both modules contain zero `sorry` tokens, and each node's `proof_deps` equals the union of its proof-step uses. The compile server did not answer the object-comparison axiom-probe request on either dry run; the delivery tool explicitly defers that probe to the merge. The item-module probe reported no forbidden axiom.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.etale_proEtale_exceptional_transport`
(node `lem-sf-etale-proetale-exceptional-transport`).

The new theorem `AlgebraicGeometry.ProEtale.exceptionalTransport_constructible_comparison`
(node `new-etale-proetale-exceptional-object-comparison`) is also proved.
No `sorry` remains in either delivered module; zero holes added, zero unproved split-offs.
Imported library declarations are used as stated, including dependencies that retain their own holes.

## No longer needed

Removed these direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`

The canonical compactification comparison already packages open extension, exactness, direct-image
comparison and compatibility of bounded-below with unbounded derived categories. The source
comparison API supplies the all-module Tor comparison and Hom bijections directly. The supplied
adjunction is used directly; its existence need not be proved again.

Removed these direct proof dependencies and their obsolete top-level tool approvals where present:

- `sk-thm-pe-constructible-comparison`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-sfb-finite-extension-by-zero-exact`
- `def-amb-etale-compact-support`
- `def-sfb-finite-derived-lower-shriek-compactification`
- `thm-amb-etale-exceptional-adjoint`
- `def-sfb-finite-extension-by-zero`

These are removals from this proof's direct dependency list; several notions or results remain
in transitive imports. No claim is made that every removed module leaves the targets' whole
import closure. No transport-tail module or theorem is required; the stale retained tail
reference was removed rather than delivered.

## Where the brief, the DAG or earlier work was wrong

The retained report described an absent transport-tail split, and the retained item node still
mentioned that split in its provenance/tool list. The retained object-comparison node also used
two nonexistent finite-model node IDs; these now refer to the existing proper-base-change nodes.
Its docstring blueprint ID is reconciled with its node. The new node now cites its definition dependencies directly and records the enclosing blueprint unit through the transport item; both proof-origin records identify the argument as agent-written. The DAG's earlier Step 4 unnecessarily
reconstructed an ordinary adjunction even though `adj` is a hypothesis. The proof uses that
hypothesis and the source library's canonical comparison implementations. No target statement,
existing public signature, or definition was changed.

## New nodes

`new-etale-proetale-exceptional-object-comparison`, module
`lean/Sheaf/AlgebraicGeometry/EtaleProEtaleExceptionalObjectComparison.lean`, records the proved
intrinsic bounded constructible object comparison. Its finite-model and bounded-derived
comparison dependencies are existing declarations. It introduces no remaining proof obligation.
No change record is required: existing statements and definitions are unchanged.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
