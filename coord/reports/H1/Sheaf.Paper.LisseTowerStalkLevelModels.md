## What changed

Replaced the whole-proof sorry in
`AlgebraicGeometry.Scheme.lisse_tower_stalk_level_models` by a proof from a connected
etale presentation and the existing
`AlgebraicGeometry.Etale.finiteRing_derived_local_constancy`.
The original theorem statement and its two public imports are unchanged.

The proof constructs the algebraic levels as actual derived geometric stalks of
the etale origins. Exact stalk homology transfers vanishing; finite locally constant
cohomology and the universe-lift stalk isomorphism give finite module cohomology.
Finiteness of each completion quotient follows from the already proved bijectivity
of the specified `constantAdicQuotientMap` (accessed by a proof-only `import all`).
On a connected chart, the connected-stalk clause of finite-ring derived local
constancy gives a separate etale cover at each level. Pulling it back along any
pro-etale refinement and generating its sieve gives the required marking cover.
The code writes the pullback comparison and the factorization of every sieve
member, then applies the conditional coefficient transport. It also transports
the outer covering through the canonical terminal-object isomorphism and composes
refinement arrows for relative lissity.

Added `Sheaf.Paper.LisseTowerConnectedEtalePresentation`. It records the remaining
finite-coefficient descent and scalar-normalized stalk construction, with its own
source, full proof in words and DAG node. Its `transport` field takes a supplied
etale constant-stalk isomorphism as a hypothesis; neither it nor its existence
theorem supplies any local marking or covering sieve of markings. Stalks in its
signature expand the existing exact `Point.sheafFiber` and `Functor.mapDerivedCategory`;
no new choice-based stalk or algebraic-level definition is introduced.

No existing module other than the assigned item and no node of another module is
changed. No public definition is changed, so no change record or forced adaptation
is required. The unit route is retained.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Scheme.lisse_tower_stalk_level_models`
(node `lem-weil-pbc-lisse-tower-stalk-level-models`). The assigned module has zero
remaining direct sorries. Its three private helpers are proved completely:
`etale_cover_sieve_mem`, `stalk_homology_finite`, and
`connected_presentation_markings`.

Added exactly one whole-proof sorry:
`AlgebraicGeometry.Scheme.lisse_tower_connected_etale_presentation`
(node `lem-weil-pbc-lisse-tower-connected-etale-presentation`). There are no other
sorries in the delivery, including none in a definition, structure field, or
private declaration.

This is a decomposition: one upper hole closed, one strictly smaller lower
obligation added, net zero direct holes. It completes the finite-ring local
constancy, stalk cohomology and generated-cover argument rather than claiming the
entire geometric descent construction proved. The remaining theorem supplies etale
origins and their scalar-normalized actual stalk arrows; it asserts no existence of
local constant-stalk markings. The proof producing those markings is written and
checked in the assigned module.

## No longer needed

No original import was removed and no module is withdrawn or globally pruned.
The assigned node now directly uses the new presentation node, finite-ring derived
local constancy, exactness of stalks, and the specified constant quotient comparison.
The old direct dependencies for finite-coefficient origin presentation, finite-level
site comparison, bounded-below site comparison, coherent comparison pullback,
pointed geometric stalks, geometric stalk as pullback, ringed-topos tensor pullback,
adic completion modulo its ideal, and constant finite-diagram data belong to the
remaining presentation argument. They remain recorded in the new node, rather
than being incorrectly reported as globally unnecessary. Bounded-constructible
tower definitions remain statement dependencies.

`FinitePerfectAdicEtaleStalkData`, `FinitePerfectAdicStalkModels`,
`AdicResidueStalkTowerFamily`, and the coefficient-model stalk atlas were examined
but are not imported or used: their perfectness, Tor, completed-object, coefficient
presentation or universe hypotheses do not match this separately bounded relative
tower. The actual stalk functor is expanded from the existing exact point fiber
functor, so no unrelated perfect-tower theorem is imported merely for its notation.

## Where the brief, the DAG or earlier work was wrong

No false statement or change of the assigned statement was found. The DAG's first
two steps require glue not supplied by a single existing declaration: transport of
the actual normalized diagram through relative finite coefficient presentations,
bounded-below etale descent, and tensor-compatible geometric stalks. The remaining
node states that part explicitly. The third step is now implemented using the
already stated finite-ring theorem and explicit pullback covering sieves.

The recorded `FiniteCoefficientDerivedOriginPresentation` dependency currently has
a quarantine/rework entry. Its archived source was read at the listed quarantine
path. It was neither deleted nor treated as withdrawn, and this delivery does not
modify it or its attachment.

Edge cases checked against the argument: the empty scheme uses an empty etale
cover and its generated sieve; empty refinement objects use the pulled-back empty
cover; zero complexes and zero rings use exact stalks and the same finiteness
arguments; no common bound in n, finite Tor dimension, simultaneous marking cover,
or compatibility of markings is introduced.

## New nodes

`lem-weil-pbc-lisse-tower-connected-etale-presentation`, in
`dag/nodes/sec-proper-base-change/`, records connected etale origins, their actual
geometric stalks and universal consecutive scalar arrows, and transport conditional
on a supplied constant-stalk isomorphism. Source: Stacks Project, proetale.tex,
09AL (`lemma-compare-constructible-derived`), 09B1 (`lemma-compare-derived`), and
09C6 (`lemma-connected-adic-lisse`), the normalized algebraic diagram before local
constancy. It has the original chapter and unit. LeanSearch, LeanFinder, Loogle,
Mathlib grep and searches of both project roots found no applicable existing
extraction; the searches and their outcomes are recorded in the node. No change
record is added because no existing statement or definition is changed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
