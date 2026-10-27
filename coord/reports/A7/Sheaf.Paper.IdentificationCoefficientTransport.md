## What changed

Decomposed `WeilConjectures.identificationCoefficientTransport` into the finite and higher
left-adjoint normalization steps, followed by a complete formal adjunction argument. Its
signature is unchanged. `identity_mate_formula` cancels the inverse compositor, expands the
pasted counit, uses naturality of the inverse identity comparison, and applies the adjunction
triangle. `identity_stage_laws` derives the normalized counit isomorphism by conjugating a
natural isomorphism against the identity adjunction, identifies the right mate, and proves the
counit equation by naturality. The original theorem assembles those results at all its stages.

Moved the eight original data declarations, with identical names, signatures, visibility and
bodies, to `Sheaf.Paper.IdentityCoefficientTransportData`, publicly reexported by the original
module. Added the explicit left-adjoint predicate `SfIdentityCompositionLaw` there. This avoids
an import cycle between the normalization statements and their consumer; it is not a split to
avoid a compile-time limit. The two new statement modules are
`Sheaf.Paper.FiniteIdentityCompositionNormalization` and
`Sheaf.Paper.HigherIdentityCompositionNormalization`. Each has exactly one public theorem hole,
its source, and the complete argument in its docstring. No data is chosen from their existence
statements: the existing theorem concludes a proposition and eliminates those propositions.

All four delivered modules have compiled. An initial full-set run reported 81.2 seconds
for the main module; profiling the same proof after removing an unused simp argument
compiled it in 31.4 seconds, with 2.62 seconds elaboration and 5.51 seconds kernel type
checking. No declaration showed pathological unfolding. Debug profiling options were
removed before delivery. Delivery performs the final compile and axiom probes.

Change record: `coord/changes/A7-identity-coefficient-normalization-data.md`.

## Proved and sorry left

Closed the original direct hole in `WeilConjectures.identificationCoefficientTransport`
(node `lem-sf-identification-coefficient-transport`) by decomposition. This is not a fully proved
coefficient normalization theorem: the delivery adds two strictly partial left-adjoint lemmas.
The formal right-mate, normalized-counit-isomorphism and counit-equation argument is complete.

Holes added, and all holes left in the delivery:

- `WeilConjectures.finiteIdentityCompositionNormalization`, node
  `lem-sf-finite-identity-composition-normalization`.
- `WeilConjectures.higherIdentityCompositionNormalization`, node
  `lem-sf-higher-identity-composition-normalization`.

Original holes: 1. Original holes reduced: 1. New holes: 2. Item holes remaining: 0.
The data module and the two private categorical helpers contain no holes. This is a
one-to-two decomposition, with net hole count -1, not a claim that the coefficient comparison
geometry is now proved. The new statements do not contain the right-mate or counit assertions;
the finite statement also omits every other coefficient stage.

## No longer needed

Removed the original item's public planning imports
`Sheaf.Paper.CanonicalOriginCompactSupportComposition`,
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, and `Sheaf.Paper.ExchangeFunctoriality`.
Removed its private planning imports `Sheaf.Paper.QcqsCompactSupportRealization`,
`Sheaf.SixFunctors.IntegralOpenReductionComparison`,
`Sheaf.SixFunctors.IntegralCompactificationSystemRealization`,
`Sheaf.SixFunctors.AmbientProperOpenPasting`, `Sheaf.Paper.SfRationalizationKaroubi`, and
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`. The original public SixFunctorDatum
requirement is preserved through the public data-module import. The main proof uses only the
two normalization theorems and Mathlib adjunction identities already provided by that data.

The geometric nodes in old proof steps 1--4 are not globally withdrawn or claimed as pruned:
their mathematical work remains in the two new normalization nodes. No existing module is
claimed as pruned by this decomposition. Specifically,
`thm-sf-comp-composition`, `def-weil-integral-rational-qbar-compact-support`,
`lem-coef-derived-system-evaluation-calculus`, `lem-sf-integral-open-reduction-comparison`,
`lem-sf-integral-compactification-comparison-bridge`,
`lem-sf-integral-compactification-system-realization`, `def-sf-datum`, `fix-lem-exchanges`,
`lem-sf-ambient-proper-open-pasting`, `def-weil-rationalization-karoubi`, and
`def-weil-algebraically-closed-coefficients` are no longer direct proof dependencies of the
parent theorem. They remain the normalization lemmas' planned dependencies. The parent's
obsolete tool approvals for those direct uses are removed, with no approval added or reordered.
No existing module or DAG node is withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current Lean signatures do not make the DAG's normalization argument a direct application
of the existing geometric theorems. They speak about origin realizations, actual completed
comparisons, and semilinear systems, while the item speaks about the supplied datum's support
compositor. The necessary realization and coefficient-square identifications are retained as
explicit normalization steps, rather than inferred from a cited theorem's proof. This delivery
does not claim to have resolved that geometric comparison work. It proves the formal final
three steps and leaves the first four in two typed, independently claimable statements.

The composition predicate is on bounded constructible inputs so the categorical mate argument
can be applied to the exceptional-counit components without adding an unprovided finite-Tor
hypothesis on those objects. Finite compact-support identity coherence is on the ambient
bounded constructible domain; at integral coefficients the DVR gives finite Tor amplitude for
bounded constructible inputs. The statements retain all specified coefficient comparisons.
Edge cases checked in the argument: zero input, positive exponent including one, the identity
compactification, and enlarging a common finite field. No existing statement is weakened.

## New nodes

`def-sf-identity-coefficient-transport-data` records the unchanged identity comparison,
normalized counit, right mate and stage-laws definitions, together with the new left-adjoint
composition predicate. It is realized by `Sheaf.Paper.IdentityCoefficientTransportData`.

`lem-sf-finite-identity-composition-normalization` is old proof step 1 at finite coefficients:
it identifies only the specified left compositor with the canonical finite identity unitor.
It is realized by `Sheaf.Paper.FiniteIdentityCompositionNormalization`.

`lem-sf-higher-identity-composition-normalization` is old proof steps 1--4 at the other
coefficients: the completed left compositor and its rational and common-stage transport,
including all actual coefficient squares. It is realized by
`Sheaf.Paper.HigherIdentityCompositionNormalization`. It asserts none of the counit or right-mate
conclusions, which are proved in the item from the obtained left-adjoint normalization.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
