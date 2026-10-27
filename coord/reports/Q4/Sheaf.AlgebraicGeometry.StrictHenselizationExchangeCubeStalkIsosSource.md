## What changed

Repaired the return of e4102b415: removed both duplicate private declarations
AlgebraicGeometry.isIso_stalk_homology_derivedUpperStar and
AlgebraicGeometry.isIso_derivedStalkComparison_of_map from the retained replacement.
The adopted copies are private, so importing their file cannot expose them. The
replacement now imports and applies its public theorem
AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source.

Compose eA and eB with Spec of the inverse canonical small-to-full colimit
isomorphisms. smallStrictHenselizationColimitIso_toBase proves that their maps to S
and T are the original jA and jB. A local transfer argument substitutes those maps
before applying the adopted theorem, so the point equations, cartesian squares and
canonical derived comparison agree by equality and proof irrelevance. There is no
repeated inverse-image, homology or stalk proof.

The assigned old file remains a withdrawn stub. Its exact original small-model
statement is preserved, with only the distinct smallModel_ declaration name, in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeStalkIsosSource. The
adopted theorem has explicit full strictLocalization presentations; the replacement
has explicit strictHenselizationScheme presentations. No statement is weakened.

Updated the existing node from the current source, changing only lean, proof,
proof_deps and proof_origin. Added one attachment node for the existing fully proved
adopted theorem; this creates no Lean declaration. The structural comparison's
existing node supplies the other proof dependency. Change record:
coord/changes/Q4-retire-small-model-cube-source.md.

## Proved and sorry left

The assigned source has 0 sorries before and after this repair. Holes closed: none.
Holes added: none. Split-off statements: none. No delivered Lean declaration has a
sorry, and no unproved result is introduced in a definition.

The replacement theorem
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_exchangeCube_stalkComparisons_source
is fully proved. Its signature is mechanically identical to the original node's
attached signature after changing only the declaration name. The final single-file
compile passed without errors or warnings in 4.0 seconds. The replacement and an
exact-original-signature consumer also compiled together without errors or warnings
in 9.1 and 12.0 seconds. That consumer imported both the replacement and adopted
source and printed exactly propext, Classical.choice and Quot.sound for both theorems.
Its checked source is retained as scratchpad/ExchangeCubeSourceConsumer.lean.txt;
the temporary consumer module is excluded from the delivery.

Edge cases q = 0, zero G, empty total spaces, arbitrary specified cartesian models,
and all the allowed point fields need no extra hypotheses: the transport preserves
all the original data. No target signature or adopted source file is changed.

## No longer needed

Removed both duplicate private helper declarations named in the return. Removed the
private import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeClosedStalk
from the returned replacement: its geometric proof is already encapsulated by the
adopted public source theorem. That small-model module is not withdrawn; other DAG
obligations may still need it.

The original node's direct proof dependencies
lem-weil-pbc-strict-local-base-change-closed-stalk,
def-weil-pbc-derived-inverse-image and
lem-weil-pbc-abelian-exchange-cube-comparisons are replaced by the structural-map
comparison and adopted full-model source theorem. The latter two old definition
nodes remain statement dependencies, and the public comparison-map import remains
necessary for the signature. The adopted proof still uses the closed-stalk theorem.
No adopted declaration or dependency is deleted, and no net module pruning is claimed.

Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource stays retired
through deleted.txt, as in the returned packet. Its original mathematics is retained
in the replacement. The live parent node
lem-weil-pbc-strict-henselization-exchange-cube-source-stalk-iso continues to cite the
same original node id and unchanged statement. No node realized by unit sk-thm-p1,
unit statement, or unit proof step is bypassed. There are zero current Lean importers
of the old withdrawn module, so no consumer adaptation is needed; the retained DAG
parent is why its small-model statement is preserved.

## Where the brief, the DAG or earlier work was wrong

The returned packet copied two private helpers already proved in the adopted source.
They are now deleted, not renamed or restated with cosmetic changes. Directly reusing
the public theorem through the canonical model comparison repairs the exact complaint
and gives a shorter proof. All adopted declarations and imports remain unchanged.

The generic brief describes a holed item, but the retirement assignment has zero
holes and an already withdrawn item source. The DIFFERENT retirement row still
requires preservation of its small-model statement. Simply attaching it to the
full-model theorem would omit the actual transport checked here. No current rework
row or quarantine path names this item. Comparison with the current node preserves
all maintainer-owned fields, statement, stmt_deps, chapter and unit.

## New nodes

lem-weil-pbc-full-strict-local-source-cube-comparison attaches the existing public
AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source
in WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource.
It explicitly records the full strictLocalization presentations, has the exact
adopted signature and describes its already complete proof. It adds neither a Lean
statement nor a hole. Its searches were run through msearch.py and recorded; none
found this project theorem in Mathlib. Its source is the adopted module and Tags
03Q9/03QO, and its blueprint place is the source ΦS comparison in the original
geometric-stalk diagram. The new node and the structural-map comparison are in the
same unit sk-thm-p1.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
