## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_sectionGeometry` from the finite
constant-ring normalization and the existing ordinary inverse/direct-system, derived
evaluation and tensor-localization declarations. The proof constructs the system Hom
bijection, checks its naturality, builds its adjunction and derives its component unit
formula. A proved private lemma derives the unit equation from transpose compatibility
in arbitrary categories, avoiding scheme-specific rewriting through category aliases.
It then assembles the actual generic and constant-coordinate geometry, retaining
the prescribed finite adjunction package. The level push-underlying comparison is constructed
with identity components, so the final section identity is proved by reflexivity.

Added `Sheaf.Paper.TowerClassFiniteSectionInverseImages`, containing the strictly finite
normalization obligation, with a complete source-based proof plan. This statement constructs
no system functor, no derived category operation, no Base and no Geometry. All the ordinary
system and derived assembly is discharged in the item module. The new theorem is used only
inside a proof; no definition chooses an arbitrary witness from it.

All added imports in the item are private proof imports; the existing public import and
existing theorem signature are preserved. `import all` makes existing proved private
categorical helpers available without changing those source modules.

Validation: the finite lemma module compiled cleanly in 53.1 seconds; the completed item
compiled cleanly in 20.4 seconds. The original theorem signature was checked verbatim
against the repository, and the delivered files contain no profiler options or long lines.

## Proved and sorry left

Closed one direct hole: `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_sectionGeometry`
(node `lem-sfb-tower-class-section-geometry-existence`). There are zero direct holes left in
the item module.

Added one hole: `AlgebraicGeometry.ProEtale.SpTowerClasses.finite_sectionInverseImages`
(node `lem-sfb-tower-class-finite-section-inverse-images`), the whole proof of the single
public theorem in its new module. This is a decomposition, with net hole change zero,
not an assertion that the entire geometry construction is now axiom-free. No other holes
are introduced or changed.

## No longer needed

The original item had only its public statement import, which is retained. No existing
module is withdrawn. The following planned dependencies are unnecessary for this proof:

- `lem-sp-strict-system-geometric-realization`, module
  `Sheaf.Paper.SmoothPurityStrictSystemGeometricRealization`: only a Base is needed; use
  `strictBaseCoordinates` directly. The Operations and scalar/mate three-index coherences
  do not enter this existence statement.
- The full `semilinearGeometryOrdinary` and `semilinearGeometryBaseExistence` existence
  theorems are not applied, because their choices do not retain the prescribed finite
  right adjoints. Their modules remain needed for proved private naturality, exactness,
  and canonical derived-transpose helpers. Their nodes are retained in the proof graph.

`def-weil-pbc-proetale-operations` moves from a direct proof dependency to the finite
normalization node. Its definitions and canonical adjunction remain essential; this is
not a request to prune that module. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent plan correctly requires prescribed finite adjunctions, but the conclusion of
`semilinearGeometryOrdinary` only retains coefficient rings, transitions and inverse images;
it does not retain prescribed level pushforwards or their underlying comparison. Applying
that existence theorem alone cannot establish the requested identity on sections. The
proof instead assembles its ordinary system construction from the supplied finite data.

The rework table records an older quarantine caused by `SfP1ProjectionTraceFalseTail`.
The current item is present with its real theorem and no such import. This delivery preserves
its attachment and proves that current theorem; it neither deletes nor replaces an archive.

## New nodes

`lem-sfb-tower-class-finite-section-inverse-images` records precisely the finite constant-ring
algebraic lift, adjacent quotient square and normalization of the specified module transpose
by the set-sheaf adjunction. Tensor insertion and its scalar-multiplication inverse supply
the proof plan. Empty schemes and level zero require no special hypothesis, and no flatness
of a quotient ring map is asserted. Its module is
`Sheaf.Paper.TowerClassFiniteSectionInverseImages`. The blueprint search for finite
constant rings found only closed-immersion exactness and full-faithfulness nodes; neither
states this normalization. The algebraic inverse-image and underlying-identification nodes
are generic finite sheaf tools, used without bypassing a diagonal-tower unit step.
There are no change records because
no existing statement, definition or external module is changed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
