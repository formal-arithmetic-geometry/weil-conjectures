## What changed

Filled `ResolvingOplaxConstraints.section_localization_unit_constraints` with its
statement unchanged. The proof lifts the normalized ordinary section comparisons
to cochain complexes and descends both unit laws through the representative tensor
square and the termwise section equivalence.

Added `Sheaf.Paper.SectionOrdinaryMonoidalConstraints`, proving
`ResolvingOplaxConstraints.section_ordinary_monoidal_constraints`. It proves the
ordinary associator and two unitor identities from the already proved concrete
comparison laws. The item packages these identities and ordinary naturality
into strong monoidal data using the fixed normalized comparison maps. Keeping the
coherence conversion in a separate theorem avoids transferring a large monoidal
structure between two presentations of the section functor. The item's
original public import is preserved; its new proof imports are the helper module,
`SectionRepresentativeTensorArrow`, and `SectionCochainMonoidalConstraints`.
The ordinary helper applies the public `internal_section_tensor_comparison` theorem
and identifies its comparisons by the public normalization uniqueness theorems.
A generic change-of-comparisons lemma transfers its three coherence laws without
unfolding the concrete sheaf tensor construction.

Added `Sheaf.Paper.SectionCochainMonoidalConstraints`, proving that an ordinary
monoidal structure with the specified comparisons induces exactly the fixed
cochain tensor and unit maps. It uses the proved source-library
`Monoidal.MapHomologicalComplex` construction. Profiling located the main file's
remaining cost in kernel checking these two comparison calculations; keeping this
proved identification separate lets every file meet the compile limit.

The item's DAG proof and dependencies now follow this implementation.

Validation: the three-module proof compiled cleanly through `lcompile.py`
(28.2 s, 36.4 s, and 46.0 s respectively for the cochain helper, ordinary helper,
and item). The delivery command recompiles the final import cleanup and performs
the required preflight checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_localization_unit_constraints`
(node `lem-pd-section-localization-unit-constraints`).

The new theorem
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_ordinary_monoidal_constraints`
(node `lem-pd-section-ordinary-monoidal-constraints`) is also proved. No holes are
added or split off, and no direct `sorry` remains in any delivered module.
`ResolvingOplaxConstraints.section_cochain_monoidal_constraints` is also proved
(node `lem-pd-section-cochain-monoidal-constraints`).
Existing dependency theorems are used as declared by the stage-3 contract.

## No longer needed

No repository modules or mathematical dependencies are withdrawn. The item's direct
use of `lem-pe-internal-section-tensor-comparison` moves into the new ordinary helper;
it remains needed there. No original public import is removed.

The separate degreewise unit calculation in the planned argument is supplied by the
existing proved cochain monoidal functor construction. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The construction already available in
`WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex` avoids repeating the
direct-sum-summand proof of the ordinary total unitor laws. The normalized ordinary
structure is provided separately to keep concrete instance reductions out of the
localization proof. No shared definition or interface was changed.

## New nodes

`lem-pd-section-ordinary-monoidal-constraints`, in
`dag/nodes/sec-poincare-duality/lem-pd-section-ordinary-monoidal-constraints.json`,
realizes the proved helper theorem in `Sheaf.Paper.SectionOrdinaryMonoidalConstraints`.
Its statement consists of the ordinary associator and two unitor diagrams for the
section equivalence and its specified comparison maps, strictly before the cochain
and derived-localization steps.
It has no derived-category hypothesis and introduces no `sorry`. There are no
change records because no other existing module or its node was changed.

`lem-pd-section-cochain-monoidal-constraints`, in
`dag/nodes/sec-poincare-duality/lem-pd-section-cochain-monoidal-constraints.json`,
realizes the proved theorem in `Sheaf.Paper.SectionCochainMonoidalConstraints`.
It identifies the induced cochain tensor and unit maps from the given normalized
ordinary monoidal maps. It retains the ambient `HasDerivedCategory` assumption needed by the existing
totalization API. Its proof privately imports `SectionDerivedTensorData` for the ordinary
comparison natural transformation and its totalization equality. It introduces no holes and covers just the total-complex
identification step, before the derived localization and unit descent.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
