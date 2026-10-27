## What changed

Replaced the proof hole in
`AlgebraicGeometry.RingedSpace.exists_free_neighbourhood_prescribed_stalk_basis`
without changing its statement or public imports. The proof now represents finite
families of module and ring germs on a common neighbourhood, spreads finite linear
combinations, constructs the finite free epimorphism with the prescribed basis
germs, restricts it using `overMap` and `mapFreeIso`, and proves the terminal
standard-generator formula after restriction. These are private proved helpers,
adapted from the scheme-level construction in
`Sheaf.AlgebraicGeometry.FiniteStalkGeneratorsNeighborhood` to arbitrary ringed spaces.

The finite-type kernel shrinking part (original steps 4–6) is isolated in the new
module `Sheaf.AlgebraicGeometry.FiniteFreeEpiIndependentGerms`. Its theorem assumes
an already constructed finite free epimorphism and only linearly independent
image germs, and concludes sectionwise injectivity near the point. It does not
lift any prescribed germs, construct an epimorphism, or conclude an isomorphism.
The item performs all that other work and combines mono and epi in the abelian
category of module sheaves. Updated the item's DAG proof to match this argument.

Validation: `lcompile.py --all` compiled both modules successfully, with no diagnostics
(the item in 19.5 seconds, the new statement module in 0.1 seconds on the final
check). A textual comparison confirms that the existing theorem signature and
all original public imports are unchanged. Each Lean file has lines of at most
100 characters.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.RingedSpace.exists_free_neighbourhood_prescribed_stalk_basis`
(blueprint `lem-trf-finite-presentation-stalk-basis-spread`). The item has zero
remaining `sorry`s. Its finite-germ, finite-span and epimorphism helpers are proved.

Added one hole in
`AlgebraicGeometry.RingedSpace.exists_injective_neighbourhood_of_independent_free_epi`
(blueprint `lem-trf-finite-free-epi-independent-germs`). Its complete proof in words
and its dependency nodes specify the remaining kernel argument. This is a
decomposition: one upper hole closed, one strictly smaller hole added, net zero
holes closed. The item still depends on `sorry` through that named theorem.

Edge cases checked in the construction and remaining statement: rank zero uses
empty tuples, finite intersections and sums; an empty space has no supplied point;
the zero stalk ring causes no nontriviality assumption; arbitrary ringed spaces
are allowed, without local-ring, scheme, Noetherian or coherence assumptions.

## No longer needed

The item no longer directly imports
`WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk` or
`WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType`.
They are retained as proof dependencies of the new kernel-shrinking theorem.
The first surjectivity shrinking is proved directly from the already proved
`exists_finite_type_local_coefficients`, by representing finite coefficients and
equalities of germs, rather than transporting 01B8 to a slice ringed space.

No existing module or node is withdrawn or globally pruned. The kernel finite-type
and stalk-surjectivity nodes remain necessary for the new theorem's documented
proof; the module-stalk, finite-presentation and module-category definitions remain
necessary. All original public imports are preserved, so no consumer adaptations
are required.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The informal DAG correctly describes
the argument, but applying its ringed-space 01B8/01BP declarations on a slice site
requires explicit reindexing to the ringed open. The completed first shrinking
avoids that interface conversion by proving its finite-coefficient argument
on the original space. The remaining theorem isolates exactly the kernel-side
conversion and shrinking. The unit route and all existing statement signatures
are preserved.

## New nodes

`lem-trf-finite-free-epi-independent-germs`, in
`dag/nodes/sec-trace-formula/lem-trf-finite-free-epi-independent-germs.json`,
states only eventual sectionwise injectivity for an already given finite free
epimorphism with independent image germs. Source: Stacks 0B8J, last two sentences
of the proof, using 01BP(1) and 01B8. It is strictly the kernel half of the item.
Mathlib searches (LeanSearch, LeanFinder, Loogle and grep), source-library searches,
and the blueprint search found no existing theorem with this generic ringed-space
statement. Its source, complete proof, Lean attachment and inherited unit are
recorded in the node. No change record is needed: no existing interface changed.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
