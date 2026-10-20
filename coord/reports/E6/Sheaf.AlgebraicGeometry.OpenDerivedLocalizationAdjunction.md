## What changed

Completed the queued retirement of Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
using deleted.txt. The current module is already proved; its distinct combined wrapper
was retained by M5's recent compatibility repair and remained queued for retirement.
No current or quarantined Lean module imports or applies it.

Attached lem-pc-open-derived-localization-adjunction jointly to the two existing upstream
components nonempty_hasDerivedCategory_openSubscheme and open_derived_localization_adjunction,
with its existing nonempty_derivedOpenLocalization dependency providing the family clause.
The attachment explicitly distinguishes the narrower primary theorem from the complete
three-clause mathematical assertion. The node's statement is unchanged. Reconciled all
six DAG parent proof descriptions with the upstream API their existing proofs already use.
No upstream Lean file, consumer statement, target, definition or unit route is changed.

Change record: coord/changes/E6-open-derived-localization-adjunction-retirement.md.

## Proved and sorry left

Actual item count: 0 of 0 sorries closed; 0 added; 0 split off; 0 left.
This is retirement of an already proved duplicate wrapper, not a newly closed proof
or a decomposition. No theorem is handed to another worker.

A validation-only copy compiled the complete unchanged former combined statement from
all three upstream components in 6.4 seconds. #print axioms for that assembly and all
three components reports exactly propext, Classical.choice and Quot.sound. The original
current module also compiled cleanly in 4.6 seconds. Scratch validation files are outside
the delivered lean/ tree. No delivered Lean declaration contains sorry. Five unchanged
upstream parents also compiled cleanly (24.4 to 54.1 seconds). The unchanged upstream
SupportedMapAffineUnionGluing validation copy exceeded 60 seconds both during concurrent
validation and when retried alone. It is not adapted or delivered; its existing source,
imports, public interface, and proof remain untouched by this retirement. No claim that
this parent was freshly compiled is made.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction, including
its unused combined theorem open_derived_localizations_and_adjunction. Its one public
DerivedCategory import and two private upstream component imports disappear with it.
Their underlying modules remain needed by existing upstream implementations and are
not claimed globally pruned. No mathematical node or proof dependency is removed.

The six retained DAG parents already use the upstream component interface. The
localization and adjunction assertions remain required and are preserved in their
current upstream locations. In particular, zero importers alone is not used to justify
withdrawal: the full original assertion is reconstructed and all parent records are
reconciled. The sk-thm-picard-duality unit statement, proof step, and realized lists stay.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a hole repeatedly split off, but this current item
has zero holes and is explicitly a retirement in coord/queue.tsv and coord/retire-items.tsv.
M5's reviewed landing 265ea3b6a00 fixed a name collision while keeping the complete
wrapper, which did not finish the hand-off requirement to retire Sheaf copies. This
packet completes the remaining withdrawal without undoing that proof or weakening the
mathematical node. The upstream twin splits the assertion into components; a direct
attachment to its adjunction theorem alone would omit two clauses, so the joint
realization is documented explicitly and checked by compiling the original full type.

The retirement inventory's six old Lean consumer names now correspond to upstream
modules. Their existing proofs already implement the replacements; changing or
restoring those source-library modules would be unnecessary. No rework row or current
return applies to the item. Searches with msearch LeanFinder/Loogle/grep and repository
rg found the exact upstream ingredients and no need for a new result.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
