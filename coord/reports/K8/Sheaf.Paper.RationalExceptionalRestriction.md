## What changed

Repaired returned head `07a957d888`. Restored the original `_hΛ` binder in
`Sheaf.Paper.RationalExceptionalRestriction` verbatim, with
`Profinite.continuousMapRingObj (PadicAlgCl ℓ)` in its second disjunct. The theorem signature,
the node statement and `lean.statement` agree with the current library's original statements.
Removed the rejected `coord/changes/K8-rational-exceptional-coefficient.md`; no statement or
definition change remains, so no `statement_change` record is needed.

The finite-extension branch uses `rationalRestrictionGlue` and the Dctf/Dbc predicate equality
from `localizingClosure_ctf_equals_bc`. The continuous-map Qbar branch uses the new
`continuousQbarExceptional_preserves_constructibleFiniteTor`, exactly as the return permits.
`compactification_localizing` supplies preservation by the lower shriek for both original
coefficient alternatives. The item constructs both restricted functors with
`ObjectProperty.lift`, proves their displayed equalities by `rfl`, and restricts the supplied
adjunction with `Adjunction.restrictFullyFaithful`. This completes the formal restriction
argument, including maps, without changing coefficients.

Updated the item node's proof, proof dependencies, proof origin and Lean note. Updated
the main theorem's proof docstring to describe the actual coefficient split and restriction
argument. Added a node
and module for the remaining coefficient-specific preservation assertion. The main module
compiles against the new module. No consumer adaptation is required: the original signature
and public imports are unchanged.

## Proved and sorry left

Closed the item hole in
`AlgebraicGeometry.ProEtale.CondensedRing.rationalExceptional_preserves_constructibleFiniteTor`
(node `sk-thm-restriction`). The item module has zero remaining `sorry` occurrences.

Added one hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousQbarExceptional_preserves_constructibleFiniteTor`
(node `lem-sfb-continuous-qbar-exceptional-preservation`). This is a decomposition: one upper
hole closed, one smaller preservation hole added, net zero holes. Existing imported theorem
holes are unchanged. No hole is placed in a definition and no data are chosen from a mere
unproved existence theorem.

The new theorem still needs the affine-chart exceptional comparison and the affine-space
purity and rational open-direct-image calculations for the actual all-continuous-map
coefficient, followed by finite-cover gluing of constructibility and Tor bounds. The existing
finite-subextension-valued Qbar lemmas cannot supply these calculations. Its docstring and
node record the route, the supplied-adjunction comparison, scalar transport, and empty-scheme
and zero-complex cases. Searching the library found no matching coefficient-specific theorem;
`exceptionalInverseImage_exists` is above this item and imports it, so cannot be used here.

## No longer needed

Removed these direct imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.AffineSpace`
- `Mathlib.Topology.Constructible`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.Paper.AffineSpaceRationalInduction`
- `Sheaf.Paper.ClosedAdjointConstructibleYoneda`
- `Sheaf.Paper.ClosedSupportConstructible`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`
- `Sheaf.Paper.RestrictionLocal`

Removed these direct proof-dependency edges from the item node:

- `sk-def-sfb-dc-setting`
- `def-weil-closed-immersion`
- `def-weil-pbc-scheme-conventions`
- `def-sbc-affine-space`
- `det-thm-restriction-local`
- `sk-def-sfb-constructible`
- `sk-def-sfb-bounded-constructible`
- `det-cor-affine-space-rational-induction`
- `det-prop-closed-adjoint-constructible-support`
- `det-prop-closed-adjoint-constructible-yoneda`
- `def-weil-constructible-subset`
- `lem-weil-pbc-qcqs-morphism-permanence`

The finite-extension geometric argument is encapsulated in the retained
`RationalRestrictionGlue` import; its own dependencies remain there. The continuous-Qbar
preservation node retains the unit's geometric route in its proof plan. Definitions needed
by the signature remain available through the existing public imports. These are removals
of direct imports and edges, not claims that all corresponding modules leave the targets'
transitive import closure. No Lean module is withdrawn. The rejected coefficient repair and
its change record are not delivered.

## Where the brief, the DAG or earlier work was wrong

The returned delivery incorrectly replaced the all-continuous-map coefficient
`Profinite.continuousMapRingObj (PadicAlgCl ℓ)` by the different
`Profinite.padicAlgClRingObj ℓ`. This repair restores the binder and node Lean statement,
removes the coefficient change record and corrects the old node note. It proves the E branch
using the existing route, and explicitly leaves the continuous-map preservation assertion
as the review requested. No assertion that the original statement was false is made.

## New nodes

`lem-sfb-continuous-qbar-exceptional-preservation`, in
`lean/Sheaf/Paper/ContinuousQbarExceptionalPreservation.lean`, states preservation by the
supplied localizing right adjoint for the original all-continuous-map Qbar coefficient.
It is strictly one part of the item: it does not construct the restricted functors,
their compatibility equalities or the restricted adjunction. Its source is the first two
proof paragraphs of blueprint `sk-thm-restriction`, with the coefficient convention of
`sk-def-localizing-closure`. Remaining work is listed above. No change records remain.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
