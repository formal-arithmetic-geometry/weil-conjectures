## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ResidueHomologyRankOneCoefficient.lean`
from the archive named by the current rework row. Replaced its public import of
withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` with
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, the canonical upstream module
already used by `ResidueStalkHomologyMapComparison`. The theorem, both private
helpers, signatures, proof bodies, and existing DAG attachment and route are
preserved. Change record:
`coord/changes/K4-residue-homology-rank-one-canonical-pullback.md`.

Compiled the restored module through `lcompile.py`: exit 0, 10.9 seconds, no
warnings. Read the comparison theorem and its node: its hypotheses match the
existing application, without the unnecessary negative-term condition. The proved
helpers then convert invertible residue homology to a monic degree-zero component
and use tensor balancing to obtain the nonzero rank-one coefficient. Checked the
archived parent's existing application against the unchanged restored signature.
Empty opens admit no point witness; the residue field at the given point is
nontrivial. Arbitrary frames are handled by the existing conjugation proof.

## Proved and sorry left

Zero holes in the archived item and zero in the restored item. Closed 0; added 0;
split off 0. This is a quarantine restoration and import repair, not a new hole
closure or a decomposition.

The restored `AlgebraicGeometry.residue_ne_zero_rankOne_stalk_coefficient`
(node `lem-sc-residue-homology-rank-one-coefficient`) retains its complete proof
from the existing `AlgebraicGeometry.isIso_residue_stalk_homologyMap`. The private
`mono_component_of_mono_homology` and
`residue_coefficient_ne_zero_of_mono` are proved. No sorry remains in the delivery.
No claim is made that all transitive dependencies are axiom-free.

## No longer needed

Removed the direct import of withdrawn
`Sheaf.AlgebraicGeometry.DerivedPullback`, replacing it with the canonical upstream
module. No mathematical node or module is pruned or withdrawn. The existing
`lem-sc-residue-stalk-homology-map-comparison` dependency remains necessary and
imported. The parent and the unit route remain intact.

## Where the brief, the DAG or earlier work was wrong

The assigned item is absent from live `lean/`, but it is preserved in quarantine
and has zero holes. The current rework record authorizes restoration, not deletion
or another decomposition. The archive's obsolete import must now point at the
canonical upstream derived-pullback module. The current comparison module already
contains the corresponding import repair (C1's landed change record).

Fresh searches were run with msearch leanfinder (injective residue scalar extension
of rank-one maps), loogle (`IsLocalRing.residue, IsUnit`), and grep
(`residue.*homology|homology.*residue`), plus local source searches. They find the
standard local-ring lemmas, not a replacement for the geometric comparison. The
existing complete proof is retained without new statements or nodes.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
