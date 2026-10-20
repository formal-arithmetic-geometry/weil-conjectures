## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift.
Withdraw its duplicate module using deleted.txt. Reattach
lem-sc-perfect-open-stalk-degreewise-lift to the existing proved declaration in
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift. Its canonical-comparison
conclusion implies the old existential-comparison conclusion without changing the node's
mathematical statement, dependency edges, or unit route.

Migrate the sole direct consumer, Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift:
change its private import, unpack the source theorem's g/hg pair, explicitly define eW
as the termwise canonical restriction comparison, and restate hg by definitional equality.
Its public theorem signature, docstring, attributes and public imports stay unchanged.
No source-library file changes. Change record:
coord/changes/E4-retire-perfect-open-stalk-degreewise-lift.md.

Repair of returned head 3eb7bb5dd2: rebuilt the consumer from its current shared version,
including the a68ffff8db migration to the source degreewise-shrink theorem. Retained
its canonical shrinking coordinates, comparison transport, and final component proof
verbatim. Reapplied only the source degreewise-lift import and canonical eW construction.
This resolves the overlapping consumer edit that prevented the reviewed delivery landing.
The adapted consumer compiles on the server in 3.3 seconds without warnings. The original
item's earlier compilation took 4.5 seconds. The earlier import-only migration test
fails as described in the change record. LeanFinder, Loogle and Mathlib grep searches found no closer Mathlib
result; the already proved source counterpart is the direct replacement.

## Proved and sorry left

The assigned module already had zero sorry. Holes closed: 0 of 0. Holes added: 0.
No split-off theorem and no remaining hole in any delivered module.
AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_lift is retained
as the existing complete source proof. The adapted
AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_chainMap_lift remains completely
proved. This delivery is a duplicate retirement, not a newly closed proof hole.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift. Its only direct consumer
replaces the private import with WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift.
The mathematical node lem-sc-perfect-open-stalk-degreewise-lift stays needed and is
reattached to that source theorem. All three original proof dependencies stay needed:
def-pc-perfect-complex, lem-sc-open-stalk-free-map-local-lift and
def-sc-open-module-stalk-functor. No other module or node is claimed as pruned.
No upstream declaration is removed and no proof is replaced by sorry.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but the current queue explicitly assigns a
retirement with zero holes. The source counterpart is stronger than the Sheaf signature:
it prescribes the canonical comparison instead of existentially choosing it. Therefore
an import-only migration is insufficient; the consumer must construct the canonical eW.
The retire inventory's older PROOFDIFF_UNSAFE dependency warning is resolved for this
current consumer: it compiles with the source counterpart and its existing sibling
imports, without importing both declarations of a retained dependency.
The node statement and unit route are unchanged; the Lean attachment now records the
canonical source signature and explains its realization of the existential statement.

The returned packet used the old existential-comparison shrinking interface. The landed
source shrinking theorem instead fixes canonical coordinates; the repaired packet keeps
the current consumer's transport from those coordinates. The report's earlier final-simp
explanation applied to the pre-landing consumer; the present proof ends with its existing
component simplification and rfl. No new node or proof hole was introduced by this repair.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
