## What changed

Proved all ten original theorem holes in
`Sheaf.AlgebraicGeometry.EtaleProEtaleRingedSquareRealization`, with private proved
helpers for constant-section maps and adjunction calculations. The full module
compiled in 49.2 seconds; an unused `change` tactic reported in that run was removed. Existing public declaration
signatures and definition bodies are unchanged.

The structural ring maps are identified with the unique isomorphisms of left
adjoints to sections over terminal objects. Their square is checked after
transposition and precomposition with the constant-presheaf sheafification unit.
Identity maps on sections give the direct-image module comparisons. Restriction
of constant scalars is an equivalence, so inverse mates provide the normalized
pullback comparisons, exactness, and their ordinary square. The theorem on
composition of exact derived squares transports this equality to the entire
ordinary unbounded derived category, with the specified compositors and direction.

Proof imports added: `Sheaf.CategoryTheory.DerivedExactSquareComposition`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`, and
`WeilConjectures.CategoryTheory.InverseMateEquivalence`.
The existing node's proof, proof dependencies, and proof origin follow this route.
No other Lean module is changed. No definition repair or forced adaptation is needed.
The existing proved inverse-mate and exact-derived-square composition nodes are
used as categorical tools. They preserve the required unit route: the former
only transports the specified edge adjunctions across equivalences; the latter
only descends the already established ordinary square to localization.

## Proved and sorry left

The ten original holes are in `AlgebraicGeometry.ProEtale.SfbRingedSquare`:
`coefficients`, `modulePushIsRightAdjoint`, `directComparison_existsUnique`,
`pullComparison_existsUnique`, `squareDirectComparison_existsUnique`, `ordinary`,
`modulePullAdditive`, `modulePullLimits`, `modulePullColimits`, and `derived`.
All ten are proved. Holes closed: 10 of 10; holes added: 0; split off: 0.
No holes have been added or split off. There are zero `sorry` tokens in this packet.
Existing imported theorem holes are not changed by this delivery.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `Mathlib.CategoryTheory.Localization.Predicate`

All original public imports are retained. A compilation check showed that the
existing pullback definitions require interfaces supplied through these imports;
their retention preserves the public module interface as well.

Removed direct proof dependencies:

- `lem-weil-pbc-comparison-pullback`: use the specified comparison definitions
  from `def-per-site-comparison-pullback-data`, without assuming their coherence theorem.
- `lem-pe-constant-left-module-inverse-image`: constant ring maps follow directly
  from uniqueness of left adjoints to terminal-object sections.
- `def-weil-pbc-ringed-topos-morphism`: the existing actual ring-sheaf and module
  operations suffice; no separate ringed-topos structure is constructed.
- `lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`: use the restriction
  equivalence for the original unequal site universes from
  `lem-cbc-constant-ring-module-sheaves`.
- `lem-weil-pbc-ringed-topoi-derived-pullback`: exact termwise localization suffices;
  no K-flat resolution construction is needed.
- `lem-weil-pbc-exact-functor-derived-functor`: no comparison with a separately
  constructed universal derived functor is needed.
- `lem-weil-pbc-localization-universal-property`: the already proved exact-square
  composition theorem packages the localization argument.
- `lem-weil-pbc-adjunction-lifts-group-ring-objects`: the actual RingCat-valued
  sheaf adjunction is already constructed, so no separate lifting argument is used.

The obsolete top-level `tool_uses` entries for these dependencies are removed,
with the remaining approvals kept in order. This is pruning from this item's
proof route, not a request to delete declarations elsewhere in the library.

## Where the brief, the DAG or earlier work was wrong

The old route proposed general ring-object lifting, arbitrary-site module
pullback universe transport, and K-flat derived pullbacks. These constructions
are unnecessary for these specified constant coefficients: the actual module
pushforward is transported from fixed-coefficient restriction across the
constant-section equivalences, and all four pullbacks are exact. The ordinary
comparison is the mate of the normalized direct-image square, as required by
the existing statement. No mathematical statement is disputed or weakened.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
