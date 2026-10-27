## What changed

Filled `AlgebraicGeometry.LineZeroClass.line_zero_class_exchange` in
`Sheaf.Paper.LineZeroClassExchange`, keeping its signature and all existing definitions.
Private helpers establish naturality and invertibility of the specified
compactification exchange and compact realization of a Cartier-pair arrow.
The separate supported Cartier D+ pullback result retains one hole.
The proof uses the stated field-realization and normalized section-exchange interfaces.
The node proof records the resulting route.

## Proved and sorry left

Closed: `AlgebraicGeometry.LineZeroClass.line_zero_class_exchange` (one original hole).
Added: one hole, `AlgebraicGeometry.SupportedCartierDerivedPullback.supported_cartier_derived_pullback`
(node `lem-pur-supported-cartier-derived-pullback`). This is a decomposition: one upper
hole closed and one strictly smaller supported-arrow result split off. No sorry remains
in the item module. The compact-exchange naturality, source combination, invertibility,
and fibre-realization composition are complete Lean proofs.
The theorem uses existing named library theorems whose proofs may still contain sorry;
this delivery proves the requested assembly from those interfaces.

## No longer needed

Removed the unused private import `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`.
No module is withdrawn. The direct proof does not use `thm-cbc-finite-torsion`:
the specified ambient pro-etale exchange is already a natural transformation.
It does not apply `lem-pur-cfiber-stalk` separately: `FibreFormula` explicitly uses
the fibre exchange and compact target, so its actual arrow equality follows from
Exchange and PairRealization by naturality of compact-support site comparison.
The arbitrary-pullback field-realization clause supplies the fibre pair directly,
so a second field-realization application over Omega is unnecessary.
These nodes remain wherever other statements or proofs require them.

## Where the brief, the DAG or earlier work was wrong

The planned proof is mathematically compatible with this implementation. Its fibre
step gives more surrounding interpretation than the Lean formula requires. The Lean
formula can be proved directly with the already stated arbitrary Cartesian-pair
realization clause. No target, definition, hypothesis, or conclusion is changed.

The field-realization statement is formulated for the canonical total space, while
PurityVectorBundle permits a chosen total space with an isomorphism to it. The proof
uses its arbitrary pullback clause along this isomorphism and pastes every subsequent
Cartesian pair square with it. The Kummer base-change interface records its supported
comparison by the constant restriction equation; normalization uniqueness identifies
that comparison with the exact proBeta in the requested formula.

## New nodes

`lem-pur-supported-cartier-derived-pullback`, module
`Sheaf.Paper.SupportedCartierDerivedPullback`, isolates the source's supported Cartier
Kummer pullback equation before compact pushforward. It is strictly smaller than the
item: it has no compactification, source-exchange invertibility, compact class arrow,
or geometric fibre assertion. Its docstring gives the full natural-language proof.
The attempted direct proof exposed cached abelian/ring instance differences in Ext
realization. The separately compiled coefficient-ring equality is valid, but reducing
all cached sheaf interfaces together exceeds the per-file compile limit. This packet
retains the mathematical statement and the complete assembly above it.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
