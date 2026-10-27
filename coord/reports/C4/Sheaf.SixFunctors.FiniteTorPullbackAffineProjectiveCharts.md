## What changed

Proved `WeilConjectures.GeneratorReduction.finiteTorPullbackAffineProjectiveCharts`
without changing its signature or original public imports. Added proof imports for the
existing normalized ordinary-pullback, exactness, and native tensor-unit comparisons.
The private helpers transport bounds and explicit finite-free splittings termwise and
construct the degree-zero regular-module model of the recorded tensor unit.

Added the proved geometric theorem
`AlgebraicGeometry.ProEtale.affineOpenClosedChartFactorization` in its own module.
It first enumerates source-tree leaves, pulls their constructible immersions back over
a finite affine cover, and reuses the existing proved `partition_tree` construction
from `AffineResidueLisseTree`. The generic proof is included privately with only its
geometric imports, keeping this purely geometric argument independent of the
arithmetic module's coefficient-model dependencies. The original module is untouched. It then pulls back the finite source chart covers and
records their actual maps to the original charts. This isolates the geometry from the
coefficient property rather than assuming that property survives base change.
The assigned theorem combines these factorizations with the termwise model transport.
No existing module besides the assigned module was changed.

## Proved and sorry left

Closed one of the assigned module's one holes:
`WeilConjectures.GeneratorReduction.finiteTorPullbackAffineProjectiveCharts`
(node `lem-sf-finite-tor-pullback-affine-projective-charts`).
Added zero holes. Both delivered modules contain zero `sorry`s, and the new geometric
theorem is proved. This is a proof from existing declarations, not a decomposition
into new unproved statements. Existing dependency holes are unchanged.

Validation: `lcompile.py --all` accepted both delivered modules without errors or
warnings at the enforced per-file limit. Profiling confirmed that the main theorem
elaborates in under one second; all profiling options were removed.

The construction covers empty source or target affines: the finite leaf index may be
empty, and no model is requested on empty leaves. Nonempty output leaves force a
nonempty source leaf before using its chart cover. Zero terms use rank zero; the
regular module uses rank one in degree zero. All morphism and coefficient comparisons
are ordinary pullback comparisons, before completion.

## No longer needed

No original public import was removed and no module is withdrawn. The attempted
private import of `Sheaf.SixFunctors.AffineResidueLisseTree` is unnecessary after
retaining its generic geometric proof locally; only
`ConstructibleOpenClosedRefinement` and `SchemeRefinementTree` are used for that step. The planned direct
use of `lem-weil-pbc-ringed-pullback-preserves-kflat`
(`Sheaf.Paper.KFlatRingedToposPullback`) is replaced by the existing exact ordinary
pullback and derived-counit APIs. That node is removed from this node's direct
`proof_deps`; it is still used elsewhere and remains a transitive import, so no global
pruning is claimed. The tree and pro-etale geometry dependencies are retained through
the new geometric lemma. No affine refinement of the pulled chart domains is needed:
their domains are already qcqs.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or weakened. The original geometric plan described grafting
base-changed trees; the proof instead reuses the already proved constructible-immersion
partition construction. The algebraic plan invoked K-flatness explicitly; existing
ordinary-pullback exactness and counit comparisons give a shorter implementation.
Imported generic completed-coefficient instances need to be excluded locally to avoid
undetermined maximum-universe constraints; no shared instance or definition is changed.

## New nodes

`lem-sf-affine-open-closed-chart-factorization`, in
`dag/nodes/sec-six-functors/lem-sf-affine-open-closed-chart-factorization.json`, records
the proved geometric half of the argument, independent of coefficient rings and
complexes. Its arbitrary property stays on the original source chart; the theorem
only constructs factorizations through that chart. The node and docstring describe
the finite affine cover, constructible immersion refinement, qcqs chart pullbacks,
coverage and the fibre-product equations. No change record is needed because only the
assigned module, its node, and this new module and node are changed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
