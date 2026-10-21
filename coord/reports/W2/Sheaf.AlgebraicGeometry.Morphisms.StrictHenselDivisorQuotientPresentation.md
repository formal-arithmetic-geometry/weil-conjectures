## What changed

Completed the zero-hole retirement of
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation`, as assigned
in `coord/retire-items.tsv`. The item is withdrawn through `deleted.txt`, and its
mathematical DAG node is attached to the already proved upstream theorem.

Adapted the sole caller,
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`.
Its original theorem signature, visibility, and docstring are unchanged. Its proof
uses the canonical small-to-full colimit comparison to identify structural maps,
applies the upstream divisor presentation, and transfers the local-base action and
universal cocone through `Ideal.quotientEquiv`. The existing regularity and localization
steps then finish the proof. The canonical comparison helper is private and proved.

Replaced that consumer's private presentation import and its public structural-map
import with their upstream owners. Updated the two existing DAG proof records to
match the upstream presentation and the consumer's transport. Mathematical dependency
lists, natural-language statements, definitions, and the unit route are unchanged.
No source-library file changes.

Change record:
`coord/changes/W2-strict-hensel-divisor-quotient-presentation-retirement.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Holes remaining: 0.
Split-offs: 0. This is a retirement repair, not a proof-hole closure or decomposition.

The retained upstream
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_presentation`
(node `lem-sbc-strict-hensel-divisor-quotient-presentation`) is completely proved.
The adapted
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_noetherian_and_local_regular`
(node `lem-sbc-strict-hensel-regular-divisor-quotient-regular-part-aux`) and its private
`comparison_base` helper are completely proved. No delivered Lean declaration contains
`sorry`, and no hole is added or moved.

Validation: the delivered consumer compiles without warnings (8.8 seconds). Its
unchanged direct importer `StrictHenselRegularDivisorQuotientRegularPart` compiles
against the adapted sandbox artifact (2.9 seconds). Explicit axiom probes of the
upstream presentation, the adapted theorem, and the direct importer's
`strictHenselizationRing_regular_divisor_quotient_part` list only `propext`,
`Classical.choice`, and `Quot.sound`. The scratch axiom probe emitted one line-length
warning for the probe command itself; the delivered source has no overlong lines.

The old consumer fails against the withdrawn empty item at line 38 with an unknown
`strictHenselizationRing_divisor_quotient_presentation`, demonstrating why the consumer
adaptation is required. All thirteen downstream modules were checked for actual name
uses; only this direct caller needs editing. No quarantined consumer was found.
The quotient transport covers `f = 0`, fields, and nonreduced rings and preserves all
original hypotheses; no target definition or statement changes.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation`.
Its duplicate public presentation theorem is replaced by the retained upstream owner
plus canonical transport inside the consumer's proof.

Removed consumer imports:
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation` (private)
and `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` (public), replaced by
their upstream owners. The latter Sheaf module remains independently used elsewhere
and is not withdrawn by this packet.

With the withdrawn item, its public imports of
`WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`,
`WeilConjectures.RingTheory.IsStrictHenselization`, and
`Mathlib.RingTheory.Localization.AtPrime.Basic`, and its private imports of
`WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation` and
`WeilConjectures.RingTheory.StrictHenselizationLocalizedDivisorQuotient` disappear from
that file. These mathematical dependencies remain used by the retained upstream
presentation or the adapted consumer; none is falsely declared globally unnecessary.
No DAG mathematical node or source-library declaration is pruned. The presentation
node's parent edge remains and its Lean attachment now points upstream.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished theorem, but the current assignment
is an explicit retirement item with zero holes. A compiling no-op would not complete
it. The small and full strict-henselization colimits are canonically isomorphic rather
than definitionally equal, so simply changing the theorem's import would not suffice.
The proof identifies both structure maps and both divisor ideals before transporting
the universal cocone.

An initial compile exposed the duplicate `strictHenselizationStructuralMap_eq` when
the old Sheaf structural-map import was combined with the upstream presentation.
The public import now uses the upstream owner, following the same correction as the
previous local-presentation retirement. This does not alter the consumer's statement.

Searches with `msearch.py` (LeanFinder, Loogle, and grep) found Mathlib's
`Ideal.quotientEquiv` and its principal-quotient API. Source searches found the complete
upstream divisor presentation and the canonical colimit comparison. These give a
complete route without any new node or split-off theorem.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
