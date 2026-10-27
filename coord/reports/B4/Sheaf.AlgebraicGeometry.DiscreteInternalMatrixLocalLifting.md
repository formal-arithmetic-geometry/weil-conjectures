## What changed

Replaced the hole in `discrete_internal_matrix_local_lifting` with a proof from a
single coefficient-section comparison, the proved `finite_local_section_lifts`,
and the regular-module scalar-extension comparison. The statement is unchanged.
The matrix is constructed explicitly by `biproduct.matrix`, with entries obtained
by `Mod.regularLift` from explicit constant sections on the profinite point.

The item proves the passage from a coefficient-section equality to the
regular-module square, using the regular-module universal property and
`Mod.regularExtensionIso_naturality`. A generic finite-biproduct entry calculation
then proves the matrix square and constructs the arrow isomorphism. The finite
biproduct comparison is a private explicit construction kept irreducible behind
its proved entry formula, so later elaboration need not expand its colimit data.

Added `Sheaf.AlgebraicGeometry.DiscreteSectionCoordinates`. Its explicit
`discretePointScalarSection` uses the actual constant-presheaf sheafification
unit at the one-point profinite set, the integer-multiple homomorphism, and the
constant-sheaf adjunction. It chooses no object from an unproved existence theorem.
Its remaining theorem compares one global coefficient section with one ordinary
constant-ring sheaf section and gives a conditional restriction formula.

Validation: `lcompile.py --all` compiled both delivered modules successfully
(26.6 s for `DiscreteSectionCoordinates`, 32.5 s for the item). All categorical
helpers are proved and private. The final file uses neither profiling nor a
transparency or heartbeat override. Factoring the matrix argument through the
arbitrary-coefficient private helper avoids expensive concrete-ring unfolding.

## Proved and sorry left

Closed the original textual hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_internal_matrix_local_lifting`.
There were 1 original holes; the item now has 0.

Added 1 hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_section_coordinates`,
in `Sheaf.AlgebraicGeometry.DiscreteSectionCoordinates`, node
`lem-sfb-discrete-section-coordinates`.

This is a decomposition, not a net hole reduction: 1 closed, 1 added, net 0.
The remaining statement asserts neither local existence nor matrix descent.
The common covering sieve, explicit matrix, regular-module square, finite
biproduct comparisons, and arrow-category isomorphism are proved in the item.
No new axiom or data hole is introduced.

## No longer needed

No modules are withdrawn and no existing public imports are removed. The
original constant-sheaf comparison and weakly-etale localization remain needed
by the new section-coordinate node; they are not claimed as pruned.

The original plan's separate transport of a covering sieve from `U.left.ProEt`
through localization and AsSmall is unnecessary: simultaneous lifting is applied
directly on the coefficient-sized site of Y after choosing the section coordinates.
The proof does not import `ScalarMatrixInverseImage`: the regular comparison is
constructed directly from the identity-underlying `mapMod` comparison and the
proved regular extension isomorphism. Its scalar-matrix and cokernel theorem is
not needed for this proof. No assertion is made that that module or its
dependencies can be removed from the library.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The initial plan identified the
required constant-ring and localization comparisons but had not supplied their
combined section restriction formula as a Lean declaration. The new node isolates
that formula at the level of sheaf sections, before all local lifting and module
matrix algebra. Unlike the original item, it has no finite ranks, module arrows,
covering sieve, or arrow isomorphism.

The empty matrix-index case is handled by the existing finite-section lemma and
biproduct universal properties. The section statement allows empty schemes and
the zero ring: all relevant section restrictions and constant sections agree
uniquely there. No nonempty or Noetherian hypothesis is added.

`lem-weil-pbc-regular-extension-comparison` is used as a proved categorical tool
from another unit. It expresses naturality of extension of scalars on regular
modules; it does not replace any step of the integral-models unit route. The
unit record is unchanged.

## New nodes

`lem-sfb-discrete-section-coordinates`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-discrete-section-coordinates.json`,
records the single-section comparison and its complete argument in words.
Its sources are Stacks Tag 03CY (`lemma-sheafification-presheaf-modules`), Tag
00YV (`proposition-functoriality-algebraic-structures-topoi`), the existing
monoidal `constantSchemeIso`, and weakly-etale localization. Mathlib and project
searches found ordinary module-sheaf section APIs and local-surjectivity APIs,
but no declaration of the required internal condensed section compatibility.
Blueprint searches found no matching node.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
