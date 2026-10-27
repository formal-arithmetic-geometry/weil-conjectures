## What changed

Replaced the sorry in `AlgebraicGeometry.SectionCompactSource.pro_section_exchange_component`
by explicit transport through the canonical comparison. The proof combines the supplied etale
exchange equation, the scalar-unit square, the supported-constant square, naturality, and one
isolated compact-support site-exchange square. All original signatures and public imports stay.
The proof imports the supported-endpoint and scalar-endpoint statements. The compact-support
square remains the general proper/open comparison obligation beneath the supported endpoint.
The supported-constant normalization in the adopted library is specialized to
`PurityFiniteSetting`; its general normalization lemmas give the stated proof plan for the
arbitrary finite coefficient ring here. The scalar proof attempt elaborated but kernel checking
exceeded the file limit (the profiler reported 65.6 seconds in type checking). Its compatibility
statement is left explicitly unproved in this partial delivery; no full proof is claimed.

## Proved and sorry left

Original hole: one, `AlgebraicGeometry.SectionCompactSource.pro_section_exchange_component`.
Its body is complete: `transport_section` combines the supplied etale equation with three
strictly smaller interface theorems. The final assigned module compiles in 5.3 seconds,
and the scalar statement module in 5.1 seconds.

The delivery adds three named holes, each with a matching DAG node:

- `AlgebraicGeometry.SectionCompactSource.compact_support_site_exchange_square`, in
  `Sheaf.Paper.CompactSupportSiteExchangeSquare`, node
  `lem-pur-compact-support-site-exchange-square`;
- `AlgebraicGeometry.SectionCompactSource.sourceComparison_exchange`, in
  `Sheaf.Paper.SectionSourceProExchangeTransport`, node
  `lem-pur-section-source-pro-exchange-transport`;
- `AlgebraicGeometry.SectionCompactSource.constant_square`, in
  `Sheaf.Paper.SectionSourceProExchangeConstantSquare`, node
  `lem-pur-section-source-constant-square`.

The combination in the assigned module is proved by Lean. This is a decomposition with one
upper hole closed and three lower holes added, rather than a net hole reduction. No definition,
instance, target statement, or source-library signature changes.

## No longer needed

The proof does not apply `lem-pur-section-source-etale-exchange` or import its module:
its conclusion is already supplied as hypothesis `he`. It does not apply the invertibility
assertion `thm-cbc-finite-level-proetale` or import
`CanonicalFiniteLevelCompactSupportBaseChange`: that assertion does not state equality of
the canonical comparison paths. The new square states the precise equality used instead.
These dependencies are removed from this node's proof route; no claim is made that other
consumers cease to need them. No existing public import or module is removed.

## Where the brief, the DAG or earlier work was wrong

The original proof step attributes a canonical exchange comparison equality to
`thm-cbc-finite-level-proetale`, whose Lean attachment provides invertibility, specialized to
Padic coefficients. Invertibility alone does not identify these maps. The new node isolates
that missing comparison equality, with a proper/open proof plan using the existing general
`compactSupportProperFactor` and `fixSiteOpenExchange`.

The assembled `compactSupportSiteComparison_open` is specialized to lifted small coefficients,
open base change and Noetherian original schemes. Its statement cannot be applied to this
item's arbitrary coefficient ring and arbitrary new base. The new statement retains the
original generality; no Noetherian or finiteness assumption is inserted.

## New nodes

`lem-pur-compact-support-site-exchange-square` records the proper/open comparison equation
before section-specific normalizations. Its module is
`Sheaf.Paper.CompactSupportSiteExchangeSquare`.

`lem-pur-section-source-pro-exchange-transport` records transport of the supported section
endpoint through that square. Its module is
`Sheaf.Paper.SectionSourceProExchangeTransport`.

`lem-pur-section-source-constant-square` records the scalar comparison endpoint used by the
categorical transport helper. Its module is
`Sheaf.Paper.SectionSourceProExchangeConstantSquare`.

Each node carries its source, proof steps, dependency declarations, and three kinds of search.
No change record is necessary because existing interfaces do not change.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
