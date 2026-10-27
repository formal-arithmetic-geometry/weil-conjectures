## What changed

Completed the listed zero-hole DIFFERENT retirement. Withdrew
Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation and retained its genuine
small-model theorem as
AlgebraicGeometry.Etale.smallModel_nonempty_strictLocalBaseChange_continuityPresentation
in Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation.
The entire declaration is byte-identical modulo its explicit smallModel_ name,
including its statement and complete assembly proof. The original small coordinate-ring
colimit, source germs, mate, target comparison and projection equations all stay exact.
The sole direct consumer StrictLocalBaseChangeGlobalHomology changes only its private
import and theorem call. The existing presentation node follows the renamed theorem;
its parent proof text names that realization explicitly. No node is deleted or added.

Change record: coord/changes/G6-retire-strict-local-mate-continuity-presentation.md.
The two other current downstream consumers are validation sources only and remain
byte-identical to the library. No source-library file or target statement is edited.

## Proved and sorry left

This is a retirement of an already proved theorem: 0 original sorry bodies, 0 holes
closed, 0 holes added, 0 remaining, and 0 split off. The complete proof of
smallModel_nonempty_strictLocalBaseChange_continuityPresentation and the direct consumer
isIso_strictHenselization_baseChange_globalHomology are retained. No definition gains
any choice or hole. The theorem applies to exactly the original universes, arbitrary
integer degrees, zero complexes and empty X, with only f assumed qcqs.

The old/new theorem source audit confirms the full declaration is identical modulo the
name. Validation compiles the retained theorem, its direct consumer, both unchanged
downstream consumers, and a separate compatibility probe importing both the canonical
and small-model presentation modules. The probe restates the original small-model
signature verbatim and proves it using the renamed theorem. Its axiom audit and that of
the renamed theorem show only propext, Classical.choice and Quot.sound. All five files
compiled without warnings (1.4, 2.8, 4.1, 6.4 and 11.4 seconds respectively); validation
sources are kept outside the delivered lean/ tree.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation.
The direct consumer no longer imports it; its model-specific statement and all actual
parent dependencies are preserved through the existing node's new Lean attachment.
The adopted canonical module and its unprefixed theorem remain unchanged.

The retained theorem needs no direct import of
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections;
the projection-formula module already imports it. That module and its nodes remain
mathematically needed. Geometry and cohomology-germ APIs no longer need public re-export
from the presentation module, so they are private proof imports; the structural-map
module supplies the statement's small-model scheme and map directly. No proof-dependency
node or blueprint unit step is pruned. The unit route and quarantined archives stay intact.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief refers to sorry holes, but coord/retire-items.tsv assigns a
zero-hole retirement. The DIFFERENT classification is essential: the adopted theorem's
mate is on strictLocalization, whereas the original theorem's mate is on
strictHenselizationScheme. Substituting the adopted theorem without transport would
change the proposition. Keeping the established small-model theorem under an explicit
name resolves the public-name collision and preserves all existing maps. Earlier node
updates already made the statement explicitly model-specific, so that node is retained
rather than redirected to a proposition about a different scheme model.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
