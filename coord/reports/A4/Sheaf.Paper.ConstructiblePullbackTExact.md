## What changed

Completed a concrete definition repair in the listed rework item
Sheaf.Paper.ConstructiblePullbackTExact. The residue-field inverses no longer come
from the complete unproved constructible-truncation existence package. The proved
lemma WeilConjectures.constructiblePullbackResidue_isUnit obtains them directly
from the characteristic of the finite base field and residue-field evaluation.
constructiblePullbackResidueUnits retains every original binder and constructs
its inverse from that lemma. Invertible is a subsingleton, so its mathematical
value and every target meaning are unchanged. The helper is valid even without
finite type and on the empty scheme.

The definition intentionally keeps the cached inverse folded during instance
comparisons and has local irreducibility to keep
its implementation out of elaboration of the pullback interfaces. Automatic size
and injectivity auxiliary generation is disabled locally. Added only a private
proof import of Mathlib.Algebra.CharP.CharAndCard. Existing public imports and
all theorem statements are retained. The standalone characteristic lemma compiled
cleanly in 2.9 seconds. The complete inline repair compiled in 44.7 seconds, with
only a class-reducibility warning. An instance_reducible experiment timed out;
the final definition deliberately retains semireducibility, with its advisory
warning scoped off for this cached class-valued construction only.
The final complete module compiled cleanly in 46.2 seconds, with no warnings.
The delivery performs its axiom probe and preflight before pushing.

The definition node now records this construction, with a separate proved lemma
node. Change record: coord/changes/A4-constructible-residue-prime-units.md.
The source consumer scan is recorded there, including all downstream modules and
the eight direct textual users. No consumer needs a source adaptation: all uses
pass these inverse structures or identify them by Subsingleton.elim.

## Proved and sorry left

Proved without sorry: WeilConjectures.constructiblePullbackResidue_isUnit
(lem-a4-constructible-residue-prime-unit). Replaced the residue-unit construction
with this proved calculation (def-a1-constructible-pullback-residue-units).

Original holes closed: zero. Holes added: zero. No decomposition or split-off
sorry. The two original holes remain, both under
lem-a1-constructible-pullback-t-exact:

- WeilConjectures.constructible_pullback_scalar_compatibility.
- WeilConjectures.constructible_point_scalar_compatibility.

The existing proved pullback t-exactness and point-fibre assembly proofs are
preserved. This packet is a definition repair, not a proof of the remaining
scalar-compatibility assertions.

## No longer needed

The definition def-a1-constructible-pullback-residue-units no longer needs
prop-constructible-truncations as a statement or construction dependency. Its
actual characteristic proof uses only the finite-field datum, ring maps, and
Mathlib. The module still publicly imports ConstructibleTruncations because its
other declarations use that interface; no module or theorem is withdrawn.
No unit route or unfinished parent dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The definition-node construction text is corrected to match the direct construction.
Both citing nodes, lem-a1-constructible-degree-zero-proper-support and
lem-zl-finite-rational-heart-comparison, still hold: their uses depend on the unique
inverse, not its source. The statement-change record retains the old text and
dependencies and audits these two citers. No mathematical hypothesis changes.

The earlier residue-unit definition obtained elementary inverse data from a large
truncation existence witness. The direct characteristic proof removes that
unnecessary dependence while preserving the unique inverse.

The planned proof imports PointRealizationStandardCohomology and
IntegralStratumChartRestrictions have no source in the shared Lean tree or its
quarantine, although compiled interfaces and their old recorded deliveries exist.
They were investigated and their recorded sources read. This packet imports
neither orphaned module and does not restore, withdraw, or alter their nodes.
The exploratory adapter and scalar-square work stays in scratchpad, outside the
delivery. The scalar compatibility holes remain explicitly reported above.

## New nodes

lem-a4-constructible-residue-prime-unit owns the proved elementary characteristic
lemma in the assigned module. It proves strictly the unit assertion needed by the
residue-unit definition, with no constructible-category or truncation hypotheses.
The existing definition node is updated to cite it. No new module and no new sorry
are added. The change record is
coord/changes/A4-constructible-residue-prime-units.md.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
