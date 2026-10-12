## What changed
Proved `AlgebraicGeometry.exists_chow_modification_data` with its existing signature unchanged.
Added the proved coordinate-reindexing theorem in `Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexImmersion`.
Its private constructions rename homogeneous polynomial variables, apply `Proj.map` in both directions,
and base change the resulting isomorphism. All proof-only imports are plain imports.
The ideal is constructed directly by Mathlib's `vanishingIdeal`, and the restriction/pullback
isomorphism proves its required property. Removed the reduced-induced-closed-subscheme import.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.exists_chow_modification_data` (node
`new-chow-modification-data`): 1 of 1 original holes proved. Added no holes; none remain in
either delivered module. Also proved `AlgebraicGeometry.exists_reindexed_projective_immersion`
(node `new-projective-reindex-immersion`). The first draft's two helper holes were both closed:
coordinate reindexing now has a proof, and `exists_ideal_restrict_iso` was removed in favor
of a direct proof in the original theorem. This is a proof, not a decomposition.

## No longer needed
Removed `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`; the old proof dependency
`lem-weil-pbc-reduced-induced-closed-subscheme` is no longer used by this node. Mathlib's
`coe_support_vanishingIdeal` suffices without the full reduced-subscheme theorem.
`lem-weil-pbc-chow-noetherian` remains used through its proved `ChowModification` interface;
its internal route is not bypassed. No unit realization is bypassed or changed.
The draft's unused helper node `new-ideal-restrict-iso` and declaration were removed before delivery.
Whether the removed import module leaves the full target closure is determined by the maintainer's ledger.

## Where the brief, the DAG or earlier work was wrong
The first draft unnecessarily left ideal support/restriction glue as a new hole, although
Mathlib directly supplies support equality and the pullback/restriction comparison.
Its reindexing hole is also provable using Mathlib's graded-ring and Proj interfaces.
The first draft failed to update the original node, used the original node's blueprint tag
for its new helper, omitted complete new-node signatures/searches, and had compiler style warnings.
These faults are repaired. The earlier DAG's full reduced closed-subscheme dependency is unnecessary.

## New nodes
`new-projective-reindex-immersion`: a proved finite-coordinate reindexing theorem, with verbatim
Lean signature, complete proof, construction sources and four search records across three required kinds (LeanSearch was unavailable). There are no
statement or definition changes to existing declarations, hence no change record is required.

## Second reading by R3
1. Compared the original module against the repository by diff: its declaration signature and
existing docstring are byte-for-byte unchanged; only proof and proof imports changed. The added
module contains no alteration to an existing library declaration. Verdict: pass.
2. Both modules compile locally without warnings. No `sorry`, forbidden axiom, unsafe/opaque
or external implementation occurs. The Chow data existence theorem uses only `propext`,
`Classical.choice`, `Quot.sound`; its chosen data therefore does not rely on an unproved existence.
All new data is explicitly constructed. Axiom probes for the final public theorems show only
the same allowed axioms. Verdict: pass.
3. Neither split-off hole remains. Reindexing is proved for every finite nonempty coordinate
type; the one-coordinate case gives n=0, an empty base/source is harmless, and the nonempty
coordinate hypothesis excludes the false empty-coordinate case. The ideal construction works
for the full open as well, when the vanishing ideal is top. Searched Mathlib with Loogle,
LeanFinder and grep, and attempted LeanSearch (service unavailable), plus both project roots with alternative terminology; reused the actual
underlying lemmas instead of adding a duplicate assumed statement. Verdict: pass.
4. The proof takes the proved upstream Chow interface, Mathlib's shortest ideal/restriction
route, and a proved reindexing construction. Proof imports are plain; imports needed by
public signatures are public. Pruning names every unused old dependency. Read
`dag/units/sk-thm-p1.json`: this auxiliary node and the removed reduced-subscheme dependency
are not unit realization steps; the unit's realized route stays intact. Verdict: pass.
5. The original node now cites the actual Chow and reindexing dependencies and describes the
Mathlib ideal/restriction proof. The new node has statement dependencies, a complete proof,
source, origin, searches, created/blueprint/chapter/unit fields and a verbatim Lean signature.
Verdict: pass.

Second reading changed: proved both helper holes, removed the ideal helper/node, pruned the
reduced-subscheme import/dependency, corrected the new node and original proof record, and
removed all compiler style warnings.
