## What changed

Completed the retirement assigned by `coord/retire-items.tsv` and the human's
2026-10-20 hand-off in `coord/changes/retire-sheaf-twins-20261020.md`.
Withdrew `Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct` through
`deleted.txt`, replaced its sole consumer's private import with
`WeilConjectures.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct`, and
redirected the existing DAG node to that source module's identical theorem.
The consumer is `Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence`;
only its import line changes. No upstream files or target statements change.
The change record is
`coord/changes/Y3-retire-discrete-action-orbit-coproduct.md`.

The current theorem statement was checked in a temporary module against the
upstream theorem, enabling the upstream file's two local forgetful instances.
That check compiled on the server in 1.3 s; `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound`. The adapted consumer compiled on the server in 1.3 s.
The temporary check was removed before delivery. The source import closure
comparison found no newly co-visible duplicate twins. A separate server compile
of the adapted consumer followed by its unchanged indirect consumers succeeded:
`Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence` (1.4 s),
`Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement` (2.1 s), and
`Sheaf.Paper.CtfHomLocallyConstant` (2.2 s). The indirect consumers were checked
from temporary sandbox copies and are not modified or included in the delivery.

## Proved and sorry left

This is a zero-hole duplicate retirement: 0 holes closed, 0 holes added, and
0 split off. `CategoryTheory.discreteContAction_finite_orbit_coproduct` was
already completely proved in both modules; its upstream proof is retained.
The withdrawn item has no remaining declarations or holes.

The adapted consumer retains its one pre-existing hole,
`Rep.normal_subgroup_ind_unipotence`, with its original signature, complete
proof docstring and DAG node. No proof in the consumer was changed.

## No longer needed

Retired module: `Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct`.
Its sole direct consumer now imports the upstream module instead. The node
`lem-exc-discrete-continuous-action-finite-orbit-coproduct` is retained and
attached to the upstream declaration; its mathematical proof plan is unchanged.

The current retired file's public imports
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets` and
`Mathlib.CategoryTheory.Limits.Shapes.Products`, and its private imports
`Mathlib.Topology.Algebra.OpenSubgroup`,
`Mathlib.Topology.Algebra.MulAction`, and
`Mathlib.CategoryTheory.Limits.Types.Coproducts`, are no longer maintained in
this duplicate file. The source theorem keeps its own imports unchanged.
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets` also leaves this consumer's import
closure; no claim is made that it can be retired globally by this delivery.
No mathematical dependency or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof obligation, but the current
queue explicitly marks this module `retire`, with zero holes. Both the copy and
the upstream twin already contain the complete same theorem and orbit proof.
The work required is removing the duplicate and redirecting its consumer and
node, rather than constructing a new proof. The existing node was still attached
to the duplicate; its Lean attachment is corrected. No mathematical statement
error was found. The source cited by the theorem is Tag 03QT,
`theorem-equivalence-sheaves-point`; its proof refers to
`pione.tex`, `lemma-sheaves-point`, whose proof decomposes a G-set into orbits.


The returned packet at `a8f2406646` passed mathematical review but did not land:
another landing changed the item after its old base `d92f73d8e`. For this repair,
the consumer and node were reconstructed from the current shared sources before
applying the retirement. The consumer still differs by exactly one private
import. The intervening A9 change had replaced the item's public G-sets import
by its upstream twin and registered `etaleFieldDiscreteForget₂` and
`etaleFieldActionForget₂` as instances; the retirement record now describes
that current version. The upstream theorem supplies the same orbit construction
using those instances locally. The exact current statement and adapted consumer
both compile. No intervening declaration or dependency change is reverted.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
