## What changed

Completed the listed retirement of
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison. Its mathematical node now
points to the unchanged, proved adopted theorem in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitComparison. The duplicate
file is listed in deleted.txt.

Adapted the sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit, preserving its public
signature, public imports, existing docstrings and private proofs. It imports the
adopted comparison and ExteriorSheafPowerComparison privately. The retired file's
proved private forward-wedge helper moves into this consumer. Its main proof now
transports the adopted local comparison through the canonical comparison
isomorphisms. Composition of the evaluated isomorphism bijections proves the
transported linear maps bijective; their wedge formula follows from tensor-section
naturality and wedge compatibility, and their restriction equation follows from
morphism naturality. The remaining generation and gluing proof stays unchanged.

Updated the item's Lean record and proof to follow the adopted proof, and the
parent's proof/dependency record to include the explicit transport. The unit route
is unchanged. Change record:
coord/changes/W4-retire-determinant-split-comparison.md.

Validation: the adapted consumer compiled through lcompile.py in 31.9 seconds with
no errors or warnings. The unchanged next direct importer,
DeterminantShortExactExists, compiled against this overlay in 7.7 seconds with no
errors or warnings. Import-direction checking confirms the new import is acyclic.
The delivery tool performs the required compile and axiom probes.

## Proved and sorry left

This is a retirement repair with zero original textual holes, rather than a new
proof of an unfinished theorem. Closed: 0. Added: 0. Split off: 0. Remaining: none.

The adopted determinant_split_comparison_exists is already fully proved.
The adapted determinant_wedgeMorphism_bijective_of_split and its moved private
exteriorSheafPowerIso_hom_wedge helper have complete proofs. No declaration is
replaced by sorry and no new public declaration or definition is introduced.

## No longer needed

Withdrawn module:
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison. Its sole import in
DeterminantWedgeMorphismSplit is replaced by the adopted twin and the canonical
comparison API. The old duplicate construction of the family and its bijectivity
is no longer compiled; the adopted theorem supplies both directly.

The comparison node no longer directly depends on
lem-sc-exterior-sheaf-power-comparison, because its adopted realization uses the
canonical exteriorPower API. That dependency now belongs to the legacy parent's
transport step and is retained there. The two linear-family dependencies remain
needed by the adopted proof. No other node or module is claimed as pruned; no
upstream declaration, signature, attribute or public import changes.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a sorry, but this item is the zero-hole
retirement listed in coord/retire-items.tsv:748. The upstream theorem and legacy
theorem express the same comparison through different exterior sheaf constructions;
a bare import replacement would not typecheck. The existing constructed canonical
isomorphisms, including their pure-wedge compatibility, supply the required bridge.

The transport uses actual evaluated isomorphisms and the adopted equivalences;
it adds no nonzero-ring, positive-rank or nonempty-open assumption and handles
rank zero with the same empty-wedge formula. No arbitrary witness is extracted
from an unproved theorem. No source-library file or target statement is edited.
There is no current rework row or W4 item-specific return. The obsolete local and
restriction nodes already lack Lean attachments and remain intact; the historical
local node still reaches the retained comparison node.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
