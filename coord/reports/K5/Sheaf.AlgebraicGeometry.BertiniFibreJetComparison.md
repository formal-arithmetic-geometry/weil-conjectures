## What changed

Replaced the body of `AlgebraicGeometry.exists_bertini_fibre_jet_comparison` with a
proof of its unchanged statement. The proof explicitly transfers a free generator
through the normalized tensor-pullback adjunction, expands the universal section,
identifies its pulled-back coefficients and values by the fibre-square and
coordinate-map identities, proves that the coefficient variables have zero relative
differential, applies Leibniz, and assembles the two tensor components into an
injective additive map.

Added `Sheaf.AlgebraicGeometry.SourceFibreDifferentialSections`, containing the
remaining differential-only geometric comparison. Its statement has arbitrary base
scheme and arbitrary source-point factorization, and contains no invertible sheaf,
section family, universal equation, singular subscheme, or value component. This is
strictly the differential-sheaf identification in steps 2–3 of the original plan;
the surrounding frame, coefficient, value, derivation and tensor-product arguments
are now Lean proofs rather than another restatement of the assigned theorem.

Added proof-only imports for `Modules.PullbackFreeGenerator`,
`Morphisms.FiberSections`, `TensorProduct.Prod`, and the new comparison module.
The original public imports and every existing public signature are unchanged.
No other existing Lean module or shared definition was edited.

Both sandbox modules compile through `lcompile.py --all`; the assigned module
took 42.4 seconds and the new module 4.8 seconds, within the 60-second limit.
The scoped heartbeat allowance documents dependent-elaboration work; the wall
time limit is unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_bertini_fibre_jet_comparison`
(`lem-zl-bertini-fibre-jet-comparison`): 1 of 1 original holes.
There is no `sorry` left in the assigned module. Its private frame, restriction,
and derivation helpers are proved.

Added exactly one hole:
`AlgebraicGeometry.exists_source_fibre_differential_sections`
(`lem-zl-source-fibre-differential-sections`). Its new module gives the source,
complete proof in words, and the exact normalization on differential germs.
This is a decomposition: one upper hole closed and one lower hole added, net zero.
The assigned theorem still depends on that hole; this is not a claim of an
axiom-free proof of the comparison. Empty source fibre, zero differential rank,
and an empty section-index type are included in the statements and construction.

## No longer needed

No existing public import was removed and no module is withdrawn.
The tentative redundant explicit import `Mathlib.LinearAlgebra.TensorProduct.Tower`
was removed; `TensorProduct.Prod` supplies the tensor equivalences actually used.

`lem-pc-proper-base-change` is removed from this node's proof dependencies: proper
base change is not used for this algebraic comparison. No proof or declaration in
its module was modified or withdrawn. The smooth finite-locally-free and
relative-differential base-change nodes are now dependencies of the new
*differential-only* node, rather than additional direct dependencies of the
assigned comparison. They remain mathematically needed and are not claimed pruned.
All other original mathematical ingredients remain in the route. No whole-module
pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old plan cites `lem-pc-proper-base-change` when using smoothness and differential
finite local freeness. That theorem is unnecessary here. The ordinary pullback
free-generator result cannot directly be applied to the tensor pullback: the
private helper uses uniqueness of left adjoints and its unit equation to bridge
the two actual constructions. The available base-change and stalk comparisons do
not directly provide the required normalized global-sections formula over an
arbitrary scheme T; that remaining step is stated explicitly in the new node.

No statement was disputed or weakened. The blueprint unit and its route are
preserved. No forced adaptations or change records are needed.

## New nodes

`lem-zl-source-fibre-differential-sections`, in
`dag/nodes/sec-deligne-laumon-general/`, states the injective A-linear comparison
between A tensor the actual cotangent fibre and sections of the ambient
relative-differential sheaf pulled back along a source-point factorization. The
formula is for one differential germ, with arbitrary scalar; the assigned proof
then handles the finite section-family sum. Sources are Stacks Tags 01V0, 02G1,
and 0098, and the node records the actual Mathlib searches. It serves the
cotangent-fibre identification in the universal first-jet argument of the same
blueprint ancestor and unit as the assigned node. The existing assigned node's
proof and dependency list were updated to match the Lean proof.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
