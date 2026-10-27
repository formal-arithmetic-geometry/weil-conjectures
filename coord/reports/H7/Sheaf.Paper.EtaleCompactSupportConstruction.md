## What changed

Replaced the hole in `AlgebraicGeometry.etaleCompactSupport_construction` by a construction
from the ordinary open-extension package and the existing coefficient-system image machinery.
The system and level open adjunctions are localized with normalized Hom-transpose formulas.
The evaluation and scalar squares are localized explicitly. Coherence is proved on the
component data before constructing the final record, avoiding repeated unfolding of that record. The derived mate comparison and
localization full faithfulness identify the scalar mate; the existing transition-localization
lemma proves the unbounded transition equation.

Added `StrictEtaleImageRestrictionConstruction`: a proved version of the existing image
assembly retaining the representative equation of its restriction square. Its private assembly
is the existing construction with that equation preserved in the conclusion. It constructs no
new functor by an arbitrary unproved existence choice.

Added `StrictEtaleOpenExtension`: the remaining ordinary construction, before complexes or
derived categories. Its structure records exact open extension on levels and systems,
adjunctions, scalar mates and ordinary transitions. The existence theorem includes a complete
construction in words, with the zero-ring, empty-open and equal-index cases checked.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.etaleCompactSupport_construction` from one
strictly smaller ordinary statement. Added one hole:
`AlgebraicGeometry.strictEtaleOrdinaryOpen_exists` in
`Sheaf.Paper.StrictEtaleOpenExtension`.

`AlgebraicGeometry.strictEtaleImageWithRestriction_exists` and its private assembly have no
holes. The main module has zero holes. All component proof terms passed kernel checking. The final clean main-file compile
passed in 43.3 seconds, with no warnings. Both supporting modules also compiled cleanly
(32.7 seconds for the derived-image construction and 13.4 seconds for ordinary data). This is a decomposition: one original hole closed and
one ordinary hole added; the net hole reduction is zero. Imported existing holes are unchanged.

## No longer needed

No original public import was removed. A redundant added proof import of
`CoefficientSystemDerivedComparison` was removed because the interface already exports it. No module or upstream declaration is withdrawn.
The extension-by-zero and constant-ring equivalence dependencies remain needed.
`lem-fix-compact-support-coefficient-change` and its module are no longer needed by this
proof: the ordinary open scalar comparison is proved directly from the extension-by-zero
presheaf formula. The broad compact-support coefficient-change theorem remains in the library
and may still be needed by other targets; no module withdrawal is claimed.
The derived construction uses the existing unbounded-comparison localization lemmas directly.

## Where the brief, the DAG or earlier work was wrong

Preflight exposed a cycle through the original broad coefficient-change dependency:
`lem-fix-compact-support-coefficient-change` reaches the current compact-support construction.
The new ordinary proof avoids it: restriction of scalars preserves the additive presheaf formula
and its unit sectionwise, and sheafification gives the normalized comparison.

The original plan combines two distinct tasks: constructing ordinary extension on strict
systems, and deriving its coherence equations. The ordinary package was not already stated
with these specified étale image and evaluation data. The sequence-site ordinary package
found by source search is specialized to the pro-étale sequence-site presentation; it does
not directly supply this interface.

The existing unbounded image assembly proves the restriction representative equation
internally but discards it when forming its returned package. The new proved assembly retains
that equation. No existing signature, target, definition or consumer was changed.

A read-only dependency traversal found a pre-existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. The unchanged live item already reaches
both nodes. This delivery does not alter either node or introduce that cycle; it is reported
for the maintainer under the process-failure rule.

## New nodes

`lem-pur-strict-etale-ordinary-open-extension`: the remaining ordinary construction from
Stacks 03S2/03DI/03DJ and Zheng Construction 4.1. Its Lean module is
`Sheaf.Paper.StrictEtaleOpenExtension`.

`lem-pur-strict-etale-image-restriction-construction`: the proved full derived-image
construction with its restriction representative equation, retaining the existing construction
of Zheng Construction 4.1 and Lemma 4.10. Its Lean module is
`Sheaf.Paper.StrictEtaleImageRestrictionConstruction`.

The item node's proof and proof dependencies now follow the Lean construction. The blueprint
unit route and all original theorem statements are preserved. A change record documents the new proof helpers, local transparency settings, and new
modules. Existing definitions, statements, and public imports are unchanged.

Generic tools from unit `sk-def-sf-operations` are used without replacing the purity unit's
route: ordinary/derived coefficient images supply the recorded geometric images;
`derivedMate_comparison` supplies the localization identity for mates; the exact-adjunction
bounds and scalar descent supply the existing image interface. The original route already
uses coefficient-system comparison. These are infrastructure for its open-extension step.

Blueprint searches `extension by zero` and `restriction representative` found fixed-coefficient
open-extension nodes and no match for the retained scalar representative package. The fixed
coefficient nodes are reused in the ordinary lemma's proof; neither new node duplicates a
blueprint statement. The ancestor tool reports `blueprint.from.node = None` for this item;
the new nodes retain that value and the item's recorded purity-step provenance.

Performance validation: profiling identified repeated large definitional comparisons and
kernel checking as the cost. The component coherence equations are proved before assembly;
the proof respects transparency and treats the quotient-ring and derived-functor definitions
as locally irreducible. Existing additive fields and fixed derived-category universe witnesses
are supplied directly. No file or proof was split to evade the time limit, and no limit was raised.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
