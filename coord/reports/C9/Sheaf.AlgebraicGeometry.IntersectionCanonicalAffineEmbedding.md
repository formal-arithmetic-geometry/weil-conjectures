## What changed

Proved `AlgebraicGeometry.intersection_canonical_affine_embedding` in the assigned module,
with its public signature and public imports unchanged. Added private, proved helpers for
inverse-image subspace stalks, the universal lift and its monicity, restriction of ambient
isomorphisms, the chart section colimit, and the stage localization isomorphism.

The proof imports the three existing assembly dependencies:
`Sheaf.AlgebraicGeometry.IntersectionStructureSections`,
`Sheaf.AlgebraicGeometry.QuasiAffineChartLimitTopology`, and
`Sheaf.AlgebraicGeometry.AffinizationLocalizationStalkCriterion`.
It uses Mathlib's affine adjunction and quasi-affine open immersion rather than rebuilding them.
The node proof now records the actual small indexing family and open-immersion argument.
No statements, definitions used by consumers, source-library files, or other modules changed.
The completed file compiled in 26.3 seconds. A local unused-variable lint option preserves
the original statement's explicitly named proof binder `he`, which its conclusion does not use.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.intersection_canonical_affine_embedding`
(node `lem-a1-intersection-canonical-affine-embedding`).
Zero holes remain in the delivered module; zero holes were added elsewhere; zero statements
were split off. All private helpers have complete proofs. The proof uses the existing stated
intersection-sections colimit, chart-limit topology, and localization-stalk criterion; their
pre-existing proof obligations remain assigned to their own modules.

## No longer needed

Removed direct proof imports:
- `Sheaf.Topology.SpectralLimitPullbackSections`
- `Sheaf.Topology.SetsInverseImageComposition`
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`
- `Mathlib.Algebra.Category.Ring.FilteredColimits`
- `Mathlib.AlgebraicGeometry.FunctionField`
- `Mathlib.Topology.Sheaves.Stalks`
- `Sheaf.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare`
- `Sheaf.Topology.FilteredSpectrumTopologicalLimit`

The following old expanded proof ingredients are no longer direct uses of this node, and
were removed from its `tool_uses`: `lem-weil-pbc-qcqs-scheme-spectral`,
`lem-weil-pbc-spectral-limit-pullback-sections`,
`lem-weil-pbc-sets-inverse-image-composition`,
`lem-weil-pbc-ring-sheafification-space-underlying-abelian`, and
`lem-weil-pbc-sets-sheaf-iso-on-stalks`. Their roles are already encapsulated in the
three existing assembly dependencies. No module or declaration is withdrawn: those dependencies
may still need these ingredients. Every current `proof_deps` entry remains used, and the unit
route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The source theorem allows an indexing type in an independent
universe, whereas the topology and stalk assembly lemmas require a small chart index.
Using all compact open neighborhoods of E, a subtype of `Y.Opens` in the scheme universe,
solves this without restricting the statement or resizing. It also avoids choosing finite
subsets of the original potentially larger index type. Empty E, a constant family, and empty
ambient W are covered by the same argument; nonemptiness is required only of the index family.

The original Lean docstring still described the expanded eight-step proof, while the current
node already provided the three assembly lemmas. The updated docstring and node describe the
actual proof. The static preflight required a change record for the namespace opening and elaboration
options, even though no public statement or definition changed. It is recorded at
`coord/changes/C9-intersection-canonical-proof-settings.md`, including all 33 import consumers.
No consumer adaptation is needed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
