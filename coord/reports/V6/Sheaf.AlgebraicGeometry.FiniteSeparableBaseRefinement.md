## What changed

Proved `AlgebraicGeometry.smooth_hProjective_proper_of_finite_separable_base` in
`Sheaf.AlgebraicGeometry.FiniteSeparableBaseRefinement`, without changing its signature.
The finite separable extension gives an etale spectrum map. The graph section into the
pullback is a monomorphism, is etale by cancellation, and is therefore an open immersion.
Its composite with the smooth second projection is the given morphism. For projectivity,
`ProjectiveSpace.liftBaseChange` lifts the existing closed immersion using the same finite
coordinate type; separatedness of the spectrum map makes the lift a closed immersion.
The proved upstream `IsHProjective.isProper` instance gives properness.

Updated the existing node's proof, proof dependencies and origin to match this argument.
Removed its obsolete top-level tool approval for `lem-kun-projective-implies-proper`.
The replacement `lem-pc-projective-proper` is already Lean-closed, hence an admissible tool
without a new approval. No unit statement or realized unit step is bypassed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.smooth_hProjective_proper_of_finite_separable_base`
(node `lem-weil-pbc-finite-separable-base-refinement`).
Added 0 holes; split off 0 theorems. No sorry remains in the delivered module.
The proof compiles remotely without warnings. An independent importing probe checks
`#print axioms` for the proved declaration returned exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
and the dependency `lem-kun-projective-implies-proper`: its holed
`AlgebraicGeometry.hProjective_properness` duplicates the already proved upstream
`IsHProjective.isProper` implication. That module is unnecessary for this item's proof;
other consumers may still need it.

Removed the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: the retained public import
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective` already exposes this API.
The projective-space module and its base-change-pullback node remain needed transitively.

The closed-immersion clause of the graph-section lemma and separatedness of the pullback
projection are unnecessary for smoothness. Its open-immersion clause suffices. The
separated-base-change node remains needed for the projective-space projection, and the
closed-immersion-cancellation node remains needed for the lifted embedding.
All other originally declared proof dependencies remain used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned final step used a separate sorry-bearing projective-properness theorem even
though the canonical upstream projectivity module already proves that implication.
The projectivity API uses an arbitrary finite coordinate type; the proof reuses that type
unchanged instead of converting it to `Fin (N + 1)`. This also handles empty coordinates
without imposing nonemptiness. The theorem statement itself needed no correction.

Read the source at Stacks `morphisms.tex`, `lemma-projective-permanence` (Tag 0C4Q),
and `more-morphisms.tex`, `lemma-smooth-etale-permanence` (Tag 0G80).
The graph proof realizes the existing DAG's smoothness route. Searches through the
prescribed leanfinder, loogle and grep tools found the etale cancellation and flat-mono
open-immersion APIs; reading the canonical projectivity module found the properness
shortcut. No new statements or definitions were necessary.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
