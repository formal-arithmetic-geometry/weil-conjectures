## What changed

Proved `WeilConjectures.compactSupportQuotient_raw_output_composition` with its
original signature. Small private conversion lemmas identify the quotient-arrow
images, coefficient-comparison components, restriction maps, and evaluated
restriction-composition components. The first three are proved by `rfl`.
For the last, congruence from `compactSupportQuotient_intrinsic_eq_ambient`
identifies the image objects, and a proved generic dependent-congruence helper
transports the natural-transformation component. Rewrite by those lemmas and
apply `compactSupportQuotient_output_composition` to `hi.2`.

Replaced the proof-only import of
`Sheaf.Paper.CompactSupportQuotientOutputTransport` with
`Sheaf.Paper.CompactSupportQuotientOutputComposition`. Removed the redundant
`import all Sheaf.Paper.CompactSupportCoefficientPresentation`; its public
interface is available through the existing public native import. Updated the
item's proof node. Local `implicit_reducible` attributes allow rewriting with
the displayed coefficient-category aliases and compact-support formulas.
No shared interface changes. The profiled proof compiled in 4.2 seconds, with
339 milliseconds of kernel checking; debugging options were then removed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.compactSupportQuotient_raw_output_composition`
(node `lem-coef-compact-support-quotient-raw-output-composition`).
There are 0 holes left in the item, 0 added holes, and 0 split-off statements.
The private helpers `rawOutput_map`, `rawOutput_comparison`,
`rawOutput_restriction`, `rawOutput_app_heq`, and `rawOutput_resComp` are fully
proved.

## No longer needed

Removed the proof import `Sheaf.Paper.CompactSupportQuotientOutputTransport`
and its proof dependency `lem-coef-compact-support-quotient-output-transport`:
only its composition component is needed. The identity half `hi.1` is unused,
with the public statement preserved. The proof does not need the output-identity
calculation or `Sheaf.Paper.CompactSupportQuotientOutputIdentity` through this
removed import. The explicit `import all` of
`Sheaf.Paper.CompactSupportCoefficientPresentation` is also unnecessary; its
public equality theorem remains used transitively, and its node remains a
proof dependency. The native dependency remains needed. No module is withdrawn;
other consumers may still use the paired transport theorem and output identity.
No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The paired output-law theorem is stronger than needed here; its existing
composition component suffices. Converting the whole equation definitionally
unfolded the large restriction-composition comparison and exceeded the kernel's
deterministic timeout. The private component API avoids this: its evaluated
comparison uses the existing functor equality and dependent congruence rather
than unfolding the comparison. No coefficient map, normalization, equality cast,
object, public signature, or target statement changed. Searches used LeanFinder,
Loogle, and Mathlib grep via msearch, together with repository searches. No new
public lemmas or nodes were needed.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
