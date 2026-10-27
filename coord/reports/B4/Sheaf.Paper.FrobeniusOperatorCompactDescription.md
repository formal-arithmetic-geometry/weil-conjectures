## What changed

Proved `WeilConjectures.TraceFormulaCoefficientConventions.frobenius_operator_compact_description`
from the two existing direct-transport normalization and compact Weil-cocycle recurrence
statements. The named theorem's signature is unchanged. No new hole or public theorem
was added.

Merged the duplicate `finiteGlobalDirectPowerTransport` construction into an abbreviation
of `compactDirectPowerTransport`, the same canonical direct power-square exchange with
the same retained compactification. This follows the project's duplicate-definition
rule and prevents the dependent Cartesian-square and pullback-model comparisons from
unfolding large derived-category models. It does not define direct transport from
repeated transport: their equality is still the separate normalization theorem.
The complete old/new construction and semantic comparison are recorded in
`coord/changes/B4-frobenius-compact-description-proof-context.md`.

The normalization module is a new public import because the abbreviation uses its
definition; both original public imports remain. The recurrence module is a private
proof import. Proved private helpers identify the direct operator with the normalized
Weil endomorphism and perform elementary categorical-power induction. The final proof
combines these interfaces by actual composition, functoriality, and induction.
The DAG now follows this proof. The unit record sk-d-weil has no realized steps;
no unit statement or route is bypassed.

## Proved and sorry left

Closed one of the item's one original holes:
`WeilConjectures.TraceFormulaCoefficientConventions.frobenius_operator_compact_description`
(node `lem-trf-frobenius-operator-compact-description`). Zero holes added, zero split
statements, and no `sorry` remains in the item. The existing imported declarations
`compact_direct_power_transport_normalization` and
`compact_weil_cocycle_endomorphism_recurrence` remain their independent proof tasks.
No definition contains a hole or takes data from a mere existence theorem.

## No longer needed

The proof uses the existing normalization and recurrence interfaces, so it does not
directly use the earlier proposed transport-iso, isomorphism-pullback, transport-induction,
iterated-Weil-cocycle, or pullback-comparison-coherence lemmas. Their uses inside those
two intermediate statements remain necessary. All three obsolete direct tool-use
approvals (isomorphism-pullback, transport-iso, and derived pullback composition) are
removed from the item's node. No module is withdrawn.

Removed the original private imports:
`Sheaf.Paper.FrobeniusPullbackComparisonCoherence`,
`Sheaf.CategoryTheory.NaturalTransportInduction`, `Sheaf.Paper.IteratedWeilCocycle`,
`Sheaf.Paper.IsomorphismDerivedPullback`, `Sheaf.Paper.FrobeniusGeometricExchange`,
`Sheaf.Paper.IteratedWeilMap`, `Sheaf.Paper.TraceFormulaCoefficientConventions`,
`Sheaf.SixFunctors.FrobeniusCohomologyTransport`,
`Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`,
`Sheaf.SixFunctors.SchemeFrobenius`, and
`Sheaf.TraceFormula.CompactFrobeniusTransportComposition`.
Their needed definitions are publicly available through retained imports. The duplicate
construction's explicit square-pasting proof and the coordinate bridge required solely
to compare two recipes are eliminated by sharing the canonical recipe.

## Where the brief, the DAG or earlier work was wrong

The current DAG already supplied the two intermediate statements needed by the proof,
but the item's private imports included neither. The item also unnecessarily reconstructed
the direct transport that the normalization module already constructs, using different
pullback coordinates. The two definitions mean the same direct map, but comparison of
their elaborated dependent presentations repeatedly unfolded large Shrink-based derived
models. The recorded definition merger fixes this while preserving mathematical content.
There are no downstream Lean consumers to adapt, as checked with downstream.py.

The latest blueprint moved this node from sk-d-weil to
sk-lem-tf-frobenius-convention; its statement is unchanged. The latest source and proof
were read. Searches through msearch.py returned unrelated field-Frobenius results,
Loogle's pow_succ, and no direct grep match. Direct library searches found the two
DAG-provided intermediate declarations. Edge cases are positive exponent one (pow_one),
coefficient level one, and zero carrier. Level zero is excluded by the original
positivity proof. No source-library or Challenge.lean declaration was altered.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
