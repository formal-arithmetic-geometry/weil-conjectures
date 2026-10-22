## What changed

Completed the DIFFERENT retirement of Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData
(coord/retire-items.tsv, row 956). Withdrew the ambiguous twin and reattached its canonical
DAG node to the unchanged WeilConjectures module. Preserved the genuinely distinct small
coordinate-ring-colimit model in StrictLocalSmallModel.MateProjectionData as
smallModel_strictLocalBaseChangeTargetIso and SmallModelStrictLocalMateProjectionData.
Their definition bodies and structure fields are byte-identical modulo these two names.
Thirteen unclaimed consumer modules have necessary import/name substitutions.
The derived-restriction theorem also makes the category of its representation parameter
explicit and confines aggressive transparency to the proof body; the resolved signature
and every mathematical proof step remain the same. This keeps elaboration under 60 seconds.
The six signatures mentioning the target isomorphism import the new data module
publicly and directly, rather than inheriting it from an unrelated public re-export.
Ten dependent DAG nodes now explicitly cite the preserved small-model construction.

Change record: coord/changes/H1-retire-strict-local-mate-projection-data.md.
The record lists all 25 original downstream modules and the effect on each, plus the
five consumers of the duplicate germ-isomorphism helper.
Repaired the return at eb36b8c5825: the direct consumer
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit
now has an explicit row in the change record's required `## Users` table, recording
its private import/theorem substitution and unchanged public signature and construction.
The downstream query confirms it is the only direct user of the retired theorem;
the four other downstream consumers already have rows. The retained Lean edits
were compared with the current shared sources; no additional source adaptation is needed.

## Proved and sorry left

This is a definition retirement with 0 original holes, 0 holes closed, 0 holes added,
and 0 holes remaining in every delivered module. No theorem is decomposed or split off.
The exact-global-sections Leray construction and all existing complete consumer proofs
are preserved. No source-library declaration or target statement changes.

The standalone compatibility probe compiled (13.1 seconds). It imports both the adopted
canonical module and the new small-model module, proves equality of the old and renamed
target isomorphisms by rfl, and constructs the fieldwise equivalence between the old and
new data structures with inverse laws by cases and rfl. Both new declarations use only
propext, Classical.choice and Quot.sound. The source-text audit independently confirms
that the target definition and all structure fields are byte-identical modulo renaming.
The full 28-module consumer batch passed without warnings through the continuity
presentation and all three final base-change consumers. This includes 14 unchanged
validation sources rebuilt against the narrower public imports; those sources produce
no git changes. The derived-restriction file compiled in 56.1 seconds, with the standard
60-second limit. Diagnostic profiler and heartbeat options were removed. The source
colimit proof also compiles using the adopted generic germ-isomorphism theorem.
After repairing the return, `lcompile.py --all` passed again for all 28 modules without
warnings (exit 0); the derived-restriction file took 45.1 seconds. The old/new code
blocks in the change record match current source and packet verbatim, and the
target definition and all structure fields match modulo the recorded renamings.

## No longer needed

The retired module Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData is no longer
imported by any consumer. The local strictLocalBaseChangeHomologyMap abbreviation had no
consumer and is removed; its adopted canonical counterpart remains unchanged.
EtaleInjectiveSectionsComparison replaces the public projection-data import by the
narrower StrictLocalSmallModel.CohomologyGerms API. SourceCocycleExactRestriction,
StrictLocalLocalizedHomGerm and StrictLocalDerivedExchangeLeray drop unused private
imports of projection data. Seven signature-bearing modules import StrictLocalSmallModel.MateProjectionData
publicly, replacing the former indirect projection-data re-export. The continuity
presentation continues to use the target isomorphism only in its proof. The exact-sections, small-model geometry and
small-model germ dependencies remain needed; none of their nodes or proofs is pruned.
The old canonical definition node remains attached to the adopted definitions, while
its former small-model consumers cite the separate small-model definition node.
The duplicate proved module StrictLocalSmallModel.DerivedCohomologyGermIso is also
withdrawn: its sole consumer StrictLocalSmallModel.StrictLocalCohomologySourceColimit
uses the identical adopted isIso_strictLocalCohomologyGermMap theorem. Its existing node
is preserved and reattached to that source declaration. The generic stalk statement
contains no choice of strict-local scheme model. No unit statement or proof route changes.

## Where the brief, the DAG or earlier work was wrong

The generic proof-worker brief refers to sorry holes, but this assignment is a listed
DIFFERENT retirement with zero holes. The adopted definitions cannot replace the old
small-model definitions by an import swap because their base schemes and structure maps
are not definitionally equal. A no-op rebase would preserve the public-name collision.
The explicit small-model names preserve every existing map without claiming an equality
between the two scheme models. The canonical and small-model DAG attachments are now
separate. No statement was weakened and no new mathematical assumption was introduced.

## New nodes

def-weil-pbc-small-model-mate-projection-data records the existing concrete target
isomorphism and the projection-data structure on strictHenselizationScheme. It has no
sorry, makes no existence or colimit assertion, and preserves zero complexes, empty
schemes and every integer degree. Its exact sections, Leray, small-model geometry and
small-model germ dependencies already have declarations. Blueprint search found no
existing blueprint node for this model-specific package; the definition belongs to the
neighbourhood-colimit and injective-complex paragraphs of the strict-henselization stalk
formula. Mathlib and source searches confirmed that the adopted package uses the other
canonical model.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
