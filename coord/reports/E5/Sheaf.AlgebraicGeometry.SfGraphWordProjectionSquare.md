## What changed

Made the three-factor graph argument explicit. SfGraphProjectionStages constructs the
first and second proper/open/proper neighborhood presentations from the existing graph
maps. It proves their graph maps proper and identifies the existing specified comparison
with B1, the whiskered middle comparison D, and inverse B2. No data is chosen from an
existence theorem and no existing definition or statement changes.

SfGraphWordProjectionSquare imports the three constituent projection squares and proves
the assigned equality by actual categorical pasting. It postcomposes with B2, uses the
B2 square, cancels the tensor image of B2 inverse against B2, and applies the D and B1
squares. A proved private lemma expresses this pasting in an arbitrary category with
an arbitrary endofunctor; the assigned theorem specializes it to tensoring by K.
The original graph comparison, coefficient compositor and projection maps are preserved. No projection is inverted.

## Proved and sorry left

This is a decomposition: one original hole is closed and three strictly smaller holes
are added (net -2), not a completed proof of the graph tensor compatibility.

The original hole closed is
AlgebraicGeometry.Etale.sfGraphCompactificationComparison_projection
(lem-sf-etale-graph-word-projection-square). Its proof from the three constituent
statements is complete. The assigned module has zero remaining holes.

The following three new public named theorems have proof exactly `:= by sorry`:

- AlgebraicGeometry.Etale.sfGraphFirstSideIso_projection,
  lem-sf-graph-first-projection-square, SfGraphFirstProjectionSquare: only the B1 square.
- AlgebraicGeometry.Etale.sfGraphSecondSideIso_projection,
  lem-sf-graph-second-projection-square, SfGraphSecondProjectionSquare: only the B2 square.
- AlgebraicGeometry.Etale.sfGraphMiddleIso_projection,
  lem-sf-graph-middle-projection-square, SfGraphMiddleProjectionSquare: only the intersection
  square D, with the common outer proper image.

SfGraphProjectionStages contains no holes. The theorems sfGraphFirst_proper,
sfGraphSecond_proper and sfGraphPresentationComparison_stages are proved. Each new
hole has its source and complete argument in its docstring and node. None is an
endpoint comparison for the whole graph construction in another guise: B1 changes
only the compactification side; B2 changes only the proper/open/proper side; D uses
only the common open intersection. The proof combines all three.

The edge cases checked in formulating these steps are the zero ring, empty schemes
and empty intersections, identity proper factors, identity supporting opens, and
unbounded objects. The maps use the existing normalized compositors and exchanges;
the inverse-square argument cancels only their isomorphism components. No added qc,
Noetherianity, Tor-amplitude or invertibility-of-projection hypothesis occurs.

## No longer needed

No existing import is removed and no module is withdrawn or declared globally unused.
The former direct dependencies of the item (ringed projection composition, derived
monoidal comparisons, proper/open tensor interchange, open projection composition and
the graph model) remain needed in the constituent calculations. They are now recorded
on the new nodes rather than asserted to be a single closed Lean step in the parent.

The search found proper direct-image composition in LowerStarProjectionComp,
EtaleProperOpenTensorSquare, and OpenImmersionProjectionComposition. They give the
individual elementary replacement identities, not the three complete graph-word
squares with their coefficient endpoints. CompactificationProjectionComposition's
compatible-tower theorem uses a different compositor and does not directly apply.
No unrelated proof imports were added, and no unit statement or unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error is claimed. The graph model alone asserts no tensor compatibility.
The previous node's single prose step included three separate graph-word tensor
calculations. This delivery separates those calculations and formalizes their assembly;
it does not claim that their sorries are proved by the existence of the graph model.

Existing graph-neighborhood words were inspected; they contain endpoint functors and
shrinking maps, but do not contain these projection squares. The new data bundles the
same underlying graph maps into EtaleGraphPresentation so that sfGraphWordProjection
can be used without redefining its projection arrow.

## New nodes

- def-sf-graph-projection-stages: explicit neighborhood presentations, the three existing
  graph factors at those endpoints, proved properness and factorization; no holes.
- lem-sf-graph-first-projection-square: the B1 tensor square, using identity normalization,
  proper composition and Cartesian proper/open interchange.
- lem-sf-graph-second-projection-square: the B2 tensor square, using the two proper
  composition identities and Cartesian proper/open interchange.
- lem-sf-graph-middle-projection-square: the D tensor square, using the two identity-top
  graph triangles and the equality of the two composite open inclusions.

All four retain the item's chapter, unit and blueprint ancestry. No change record is
required: no existing public signature, definition, attribute or public import changes,
and no consumer needs adaptation. No source-library file is changed.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
