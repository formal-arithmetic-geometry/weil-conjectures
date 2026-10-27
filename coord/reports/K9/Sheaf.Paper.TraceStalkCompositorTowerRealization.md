## What changed

`Sheaf.Paper.TraceStalkCompositorTowerRealization` now proves its original
existence theorem, with its statement unchanged, by combining a coherent integral
comparison system, strict finite germ towers, and their normalized derived descent.
The original twelve data definitions and predicates move verbatim (outside
source-docstring tags) to `Sheaf.Paper.TraceStalkCompositorTowerData`, publicly
reexported by the original module. A mechanical comparison verified identical
binders, types and definition bodies. The new strict subrecord and its forgetful
projection are explicit constructions with no holes. No source-library module,
target statement, or other group's module changes.

The main module contains complete private proofs of integral compositor
cancellation (`trf_integralCompositor`), integral counit iteration (`iteration`,
using `counitTransport` and `realizationTransport₂`), and the point-unit equation
(`pointUnit`, using `unitNormalization`). In particular, the iteration equation
is not assumed by either new construction theorem. The final record assembly
transports the strict equations along the equality of strict subdata and supplies
all integral equations with these proofs.

The proof imports `TraceStrictStalkTowers` and `TraceStalkTowerDescent` privately.
Their statements separate the original argument's finite germ construction from
its localization and normalized quotient-presentation construction. They are
strictly smaller parts: the first contains no derived or integral data, while the
second starts from already constructed strict data and does not assert any of the
three integral coherence equations proved in the parent. Their docstrings contain
the construction arguments and source citations, including the common bounded
truncation needed for arbitrary K-flat representatives.

## Proved and sorry left

Original hole closed by decomposition:
`WeilConjectures.trfStalkCompositorTowerRealization`
(`lem-trf-stalk-compositor-tower-realization`). Its combining proof is complete.

Two holes added and retained:

- `WeilConjectures.trfStrictStalkTowers`, in
  `Sheaf.Paper.TraceStrictStalkTowers`
  (`lem-trf-strict-stalk-towers`). This is the finite whole-system germ
  construction with the prescribed unit, composition and reparametrization laws.
- `WeilConjectures.trfStalkTowerDescent`, in
  `Sheaf.Paper.TraceStalkTowerDescent`
  (`lem-trf-stalk-tower-descent`). This is normalized localization of a fixed
  strict diagram, its sections comparison, and its compatibility with every
  normalized quotient presentation.

Thus one original hole is replaced by two lower holes. This is a decomposition,
not a completed proof of the whole argument or a net decrease in holes. The item
module has zero remaining holes; the packet has two, both standalone public
construction theorems. No hole occurs in a definition or private helper. The
original integral comparison dependency is used as published; its own downstream
holes are not closed by this packet.

All four delivered modules compiled together through `lcompile.py --all`.
The initial assembly compile had one unused-argument warning, subsequently
silenced by naming that implicitly unused premise `_hn`.

## No longer needed

No mathematical module or node is withdrawn or claimed pruned. The original
public imports move to the data module and are reexported. The original private
imports of `IntegralOperationsWellDefined`,
`IntegralOperationsPreserveConstructible`, and `Mathlib.CategoryTheory.Localization.Predicate`
are retained in that module. Existing localization, well-definedness, finite stalk
and bounded quotient dependencies remain needed through the construction nodes;
their relocation is not pruning. The parent proof now directly uses only the
integral-comparison existence theorem and the two construction theorems.
The unit route and target statement are unchanged.

## Where the brief, the DAG or earlier work was wrong

No original statement is marked disputed. The original ten-step prose plan does
not yet supply declarations for assembling finite stalk maps on entire
coefficient-system complexes and for normalizing their derived descent against
all quotient presentations. These are the two remaining construction results;
finite stalk coherence and bounded quotient realization alone do not provide
those assembled interfaces. The explicit integral compositor, iteration and unit
calculations do follow from the published definitions and have been proved in
Lean rather than retained among the construction hypotheses.

Factoring the shared data into a publicly reexported module is necessary to let
the two construction modules state their results without an import cycle. This
is a declaration relocation, not a repair of their mathematical content. The
only downstream module, `Sheaf.Paper.SourceSectionStalkConeComparison` (held by K6
at checking time), remains unchanged; all original declaration names and public
imports are available through the same import as before.

## New nodes

`def-trf-stalk-compositor-tower-data` attaches the original data interfaces to
their new module and records the explicit strict finite subrecord, coherence
predicate, and projection. Original definitions and predicates retain their
meaning verbatim.

`lem-trf-strict-stalk-towers` is the finite strict germ construction, using
Stacks 0F4F and 05V1, inverse-image evaluation mates, the published finite stalk
comparison, and pointed-neighbourhood reindexing. Its edge cases include exponent
one, zero complexes, identity maps and identity reparametrization.

`lem-trf-stalk-tower-descent` is the normalized Roos/localization construction on
already fixed strict data. It records the section-composition equation used in
the parent's compositor proof and agreement with every normalized quotient
presentation. Its proof uses exact point sections, both diagonal cone coordinates,
and the common bounded truncation, with no boundedness assumption on K-flat
terms. The integral iteration and point-unit equations are absent from its
hypotheses and conclusion.

Change record:
`coord/changes/k9-trace-stalk-compositor-data-extraction.md`.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
