## What changed

Decomposed the original existence proof along its ordinary/derived boundary. Extracted
all eleven existing data declarations verbatim into SequenceSiteOpenData and re-exported
them publicly from SequenceSiteOpenExtension, avoiding a proof-import cycle. The original
theorem and all existing data signatures/bodies are unchanged.

SequenceOpenCoefficientConstruction proves coherent coefficient comparison, including
summands, units, counits, composition and identities, from the actual direct-sum
sheafification comparison. SequenceOpenScalars proves scalar preservation from the
ordinary level comparisons by unit linearity. SequenceOpenDerivedTransitions proves
the actual derived transition equation by localization, retaining the extra composite
coefficient-restriction factor. The item's private derivedAdjunction proof constructs
the localized adjunction and checks its exact unit/counit normalization.

The remaining ordinary construction is a separate source result in SequenceOpenOrdinary:
its conclusion omits all scalar and derived assertions and takes already normalized
coefficient data as input. It still requires the geometric slice presentation, the
strict levelwise system construction, exactness and their ordinary transition equation.
The original theorem now combines these strictly separate pieces with complete Lean.
This is a decomposition, not a net closure of the targets' remaining holes.

Verification: all six delivery modules compile (23.5, 37.4, 55.7, 6.3, 45.4 and
14.6 seconds respectively). All four unchanged downstream modules compile against
the overlay: DiagramOpenClopenShiftModels (48.0s), SemilinearOpenClosedComplexSequence
(22.4s), SmoothPurityTowerBinaryCtfFibre (49.4s), SystemProperOpenScalarSquare (34.7s).
Their temporary copies were removed; no consumer edit is included.
The first delivery compile timed out in derived transition specialization. Profiling
identified a 33-second implicit conversion; stating the generic helper in the exact
composite form and checking the application with reducible transparency reduced the
profiled module compile to 40.5 seconds. No definition or statement was changed.

## Proved and sorry left

Original hole closed: WeilConjectures.SemilinearSections.sequenceSiteOpenExtension
(1 of 1 original proof bodies now complete).

Proved new public theorems (zero holes):
- WeilConjectures.SemilinearSections.sequenceOpenCoefficients;
- WeilConjectures.SemilinearSections.SequenceOpenOrdinary.scalars;
- WeilConjectures.SemilinearSections.SequenceOpenOrdinary.derivedTransitions.

Also proved the private derivedAdjunction helper and all private helpers. No data is
chosen in a definition from the new existence theorem; it is used only in the theorem
proof. The data module contains no sorry.

Added and remaining hole (exactly one):
WeilConjectures.SemilinearSections.sequenceOpenOrdinary,
node lem-pur-sequence-open-ordinary, module Sheaf.Paper.SequenceOpenOrdinary.
It has a source and a complete construction/proof in its docstring. Thus 1 original
hole closed, 1 strictly smaller hole added, net 0; one split-off result remains.

## No longer needed

No mathematical module or original proof step is withdrawn. The ordinary slice and
presentation dependencies remain needed by lem-pur-sequence-open-ordinary; they have
not been discarded merely because its proof is unfinished. The main module no longer
directly imports RingedSheafSliceAdjunction, DiagramSiteRealization,
RingedPresentationTransport, Adjunction.Mates or Localization.Predicate; it imports
its four actual proof results and Localization.Adjunction. Those first three generic
results are recorded in the remaining ordinary lemma's proof plan. The data module
keeps only statement imports. The original module's original public interface is
preserved via the public data import and its remaining original public imports.
An unused scalar-naturality helper and unused Localization.Adjunction import were
removed from SequenceOpenScalars. No source-library declaration/import was altered.
Pruned mathematical modules: none.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The generic ringed-slice and diagram theorems are homogeneous
in their site/coefficient universes, while this item has independent universes and
requires normalized level comparisons. Applying a generic slice existence theorem
alone does not fill the ordinary record. The generic DiagramSiteRealization theorem also uses a constant coefficient ring;
it does not directly construct the varying-coefficient module extension.
This is the remaining substantive construction,
not an unsupported dependency or a restatement of the scalar/derived package.
Empty opens, zero coefficient rings, identity indices and non-flat coefficient maps
are admitted: none of the proved coefficient/scalar/localization arguments adds a
hypothesis. The remaining ordinary statement quantifies any normalized coefficient
datum; its summand normalization fixes the comparisons used in its transition formula.
The unit's realized route is retained; no unit statement or proof step is bypassed.

## New nodes

lem-pur-sequence-open-coefficients owns the proved coefficient construction.

lem-pur-sequence-open-scalars owns the proved preservation of actual scalar endomorphisms.

lem-pur-sequence-open-derived-transitions owns the proved descent of the ordinary
transition equation with all localization factors.

lem-pur-sequence-open-ordinary owns the one remaining ordinary existence theorem.
Its source is the original proof's steps 1, 2, 5 and 6; these are a genuinely separate
ordinary result, with no scalar or derived conclusion.

def-pur-sequence-open-derived-data owns the five existing scalar/derived definitions
previously attached to the existence theorem. def-pur-sequence-site-open-data is
updated only in its Lean attachment to the new data module. The main node's proof
and dependencies follow the combination written in Lean. Its statement dependency
list adds the two definition owners without altering its mathematical statement.

Change record: coord/changes/C6-sequence-open-data-extraction.md.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
