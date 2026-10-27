## What changed

Proved `AlgebraicGeometry.cartesian_closure_refinement` in
`Sheaf.Compactification.CartesianClosureRefinement`, preserving its exact signature.
For h = j ≫ b, construct P = h.image ×_Xbar V and W = h.image ×_Ybar Y.
The canonical map e : P → W is open since its composite with W → h.image is open;
it is proper since P → Y is proper and W → Y is separated. The dense map X → W
factors through e, so e is dominant and its closed range is all of W. Thus e is an
isomorphism, and v = inv e ≫ (P → V) is the required closed immersion. The proof
checks every projection identity and the empty case. This is the existing clopen
argument formulated using pullbacks and the proper-open-isomorphism criterion.

Updated `lem-sf-cartesian-closure-refinement`'s proof, proof dependencies and proof
origin to match the Lean argument. No unit statement or unit proof step is changed.

Made NagataSketchClosure a private proof import, removed unused RefinementCategory,
Proper-extension and VeryAmple imports, and added the private Mathlib IsIso import.
Change record: `coord/changes/M6-cartesian-closure-proof-imports.md`.
No consumer imports this module currently; the unfinished parent nodes and this
module's public statement remain intact. No other modules were edited.

Validation: lcompile.py compiled the final proof in 7.7 seconds with no warnings or
errors. A temporary `#print axioms AlgebraicGeometry.cartesian_closure_refinement`
reported exactly `[propext, Classical.choice, Quot.sound]`; the diagnostic command
was removed for delivery. The delivery tool performs the final compile and checks.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.cartesian_closure_refinement`
(blueprint: `lem-sf-cartesian-closure-refinement`). Zero holes remain and zero holes
were added; zero statements were split off. No definitions or axioms were added.
The complete proof is sorry-free transitively, as the axiom audit confirms.

## No longer needed

Removed imports:

- `WeilConjectures.Compactification.RefinementCategory`: the conclusion explicitly
  supplies proper comparison maps and all identities, without bundling refinements.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`: Mathlib's
  `IsProper.of_comp`, base-change and composition instances suffice.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`: closed-immersion base change
  is already a Mathlib instance; no ampleness statement is needed.

`Sheaf.Compactification.NagataSketchClosure` is retained as a private proof import;
only its public re-export was removed. All mathematical dependencies of the original
node are still used, with the category-of-refinements node serving to interpret the
supplied comparison data. No nodes or modules are withdrawn, and no source-library
declarations are removed. No global target-closure pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The attachment of `lem-pc-closed-imm-base-change` names
`AlgebraicGeometry.IsVeryAmple.pullback_of_field`, which is not the closed-immersion
base-change assertion needed in this proof. Use the already proved Mathlib base-change
instance for `IsClosedImmersion (pullback.snd a b)` directly. The node's mathematical
assertion remains a valid dependency; this delivery does not edit its attachment.

The original six-step plan is valid, but constructing T = Xbar ×_Ybar Y and handling
its clopen complement pointwise is unnecessary. The proper, open, dense comparison
P → W above implements that argument through existing APIs. No extra geometric
hypotheses or reducedness assumptions are needed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
