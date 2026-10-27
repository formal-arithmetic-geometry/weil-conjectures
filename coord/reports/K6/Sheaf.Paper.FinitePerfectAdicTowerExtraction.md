## What changed

Replaced `AlgebraicGeometry.Scheme.finitePerfectAdicTower_extraction`'s sorry with a proof
that constructs the common pro-etale cover and the isomorphism of complete diagrams.
Its signature is unchanged. On each chart the proof applies the existing proved
`finite_lisse_tower_section_cover`, composes its cover with the etale chart cover, and
uses the section reduction equations to prove consecutive naturality. `NatTrans.ofOpSequence`
then supplies all composite naturality equations; invertible components give a natural
isomorphism. Every object of the generated sieve is handled by its factorization through
a covering object, with evaluated sections restricted along that factorization.

Two strictly finite-level preparation obligations are stated separately. The first gives
one normalized algebraic tower per etale chart and separate, potentially unrelated,
finite-level markings. The second, for a supplied tower and those markings, gives finite
Isom sheaves, reductions and their evaluation squares. Neither asserts existence of a
common pro-etale cover or compatible sections. Thus neither is the original obligation
under another name: the common-cover compactness argument and diagram assembly are
performed in the item using the existing finite-lisse theorem.

Moved the unchanged original data and the constant-functor exactness proof into the
publicly reexported `FinitePerfectAdicTowerData` module to avoid an import cycle with the
preparation modules. Added two concrete convenience definitions for the algebraic model
diagram and composition of a pro-etale object with an etale chart. The new predicate
`FinitePerfectAdicLevelMarkings` records separate local markings using actual finite
coefficient realizations. No data are chosen in definitions from unproved existences.

Change record: `coord/changes/finite-perfect-adic-tower-data.md`.

Validation: all four delivery modules compile (4.5–8.4 seconds each). The unchanged
direct importers `FinitePerfectAdicComplexRoos`, `FinitePerfectAdicQuotientDiagram` and
`FinitePerfectAdicTowerLimit` compile against the delivery (10.5–12.7 seconds each).
Their temporary byte-identical sandbox copies were removed after this check.

## Proved and sorry left

Original holes closed: one, `AlgebraicGeometry.Scheme.finitePerfectAdicTower_extraction`
(node `lem-weil-pbc-finite-perfect-adic-tower-extraction`). Zero sorries remain in the item.

Two holes added, each the entire proof of its public theorem:

- `AlgebraicGeometry.Scheme.finitePerfectAdic_stalk_models`, in
  `Sheaf.Paper.FinitePerfectAdicStalkModels`, node
  `lem-weil-pbc-finite-perfect-adic-stalk-models`.
- `AlgebraicGeometry.Scheme.finitePerfectAdic_isomorphism_sections`, in
  `Sheaf.Paper.FinitePerfectAdicIsomorphismSections`, node
  `lem-weil-pbc-finite-perfect-adic-isomorphism-sections`.

This is a decomposition, not a complete mathematical proof of tower extraction: one
upper hole is closed from two strictly finite-level obligations and a previously proved
common-section theorem. The delivery adds one hole net if both new obligations enter the
targets' import closure. The data module has zero holes; all moved bodies are unchanged.

## No longer needed

The wrapper `lem-weil-pbc-compatible-finite-derived-trivializations` and module
`Sheaf.Paper.CompatibleFiniteDerivedTrivializations` are not used by this proof. It directly
uses the wrapper's underlying `lem-weil-pbc-finite-lisse-tower-section-cover` for the
covering step, while coefficient-sensitive evaluation is isolated in the finite-level
bridge. No existing module is withdrawn, and no global pruning claim is made: other
consumers can still use the wrapper.

The six original public imports move with the data and remain publicly available; none
is removed from the exported interface. Other original proof dependencies are retained
in the preparation nodes where their descent, stalk and coefficient-comparison steps
are used. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan omitted two substantial interface bridges. The existing finite-derived
trivialization API uses fixed-ring module sheaves and the lifted coefficient universe;
the item uses intrinsic sheaves of modules, the smaller algebraic localization, and the
actual strict derived reduction diagram. One cannot apply its compatible isomorphisms
directly to `FinitePerfectAdicLocalTower.comparison`. The finite-level bridge now names
exactly the missing coefficient transport, normalization and restriction squares.

The original node grouped normalized algebraic stalk extraction, finite Isom preparation,
common-cover construction and diagram assembly into one sorry. The new nodes separate
the first two from the last two. Existing signatures and the mathematical statement are
preserved. Searches used LeanFinder, Loogle, grep and LeanSearch; no exact Mathlib match
was found. The finite-lisse tower section-cover theorem in the project supplies the
common-cover argument, so that argument is not split off again.

Edge cases checked in formulating the two remaining statements: the empty base uses an
empty cover; zero rings and zero complexes give the same finite Isom construction;
markings may depend on n; reduction maps of Isom sheaves need not be surjective; the
arrows into the generated sieve are arbitrary, and the evaluation theorem includes exact
restriction along them. No completeness of A or M, inverse-limit comparison or perfect
A-model is asserted.

## New nodes

`def-weil-pbc-finite-perfect-adic-tower-data` attaches the original tower and realization
data, now in `Sheaf.Paper.FinitePerfectAdicTowerData`, with two concrete convenience
definitions. It contains no new existence assertion.

`lem-weil-pbc-finite-perfect-adic-stalk-models` states steps 1 and 2 of the original plan
plus independent finite-level markings on each connected chart. It has a source and a
complete natural-language proof in its docstring and node.

`lem-weil-pbc-finite-perfect-adic-isomorphism-sections` states the finite-level Isom-sheaf,
normalization and scalar-transport bridge. Its conclusion contains no common cover or
compatible sections. Its source and proof explain the existing normalized evaluation
API and the coefficient comparisons still to be connected.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
