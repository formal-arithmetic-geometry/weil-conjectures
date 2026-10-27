## What changed

Proved `Padic.primeToEll_linear_image_finite` from the existing stable-lattice finite-reduction
and congruence-kernel rigidity declarations. Added their modules as private proof imports and
used Mathlib's first isomorphism theorem. The given spectral-norm and module topologies are
transported explicitly. Finite reduction kernels are open normal subgroups, so the hypothesis
gives coprimality of each reduction image. Rigidity and the field-basis coordinate formula show
that the representation kernel contains the first open reduction kernel. Its finite quotient
then identifies with the representation image. This works with the empty basis as well.

Validation: the single-file `lcompile.py` compile passed without warnings in 6.4 seconds.
Both added proof imports were checked for import cycles.

Updated the item's existing DAG proof to the actual Lean assembly. No signatures, definitions,
public imports, other modules, or unit routes changed.

## Proved and sorry left

Closed 1 of 1 holes: `Padic.primeToEll_linear_image_finite`.
No holes remain in the item, and no holes were added or split off.
The existing inputs `Padic.exists_stable_lattice_finite_matrix_reductions` and
`Padic.coprime_congruence_kernel_rigidity` retain their existing holes in their own modules;
this delivery proves the assigned assembly from those stated dependencies.

## No longer needed

Removed the direct proof imports `Sheaf.RepresentationTheory.ProfiniteStableLattice`,
`Mathlib.Topology.Algebra.Valued.LocallyCompact`, and `Mathlib.GroupTheory.OrderOfElement`.
The lattice and power-map arguments are now provided through the two existing DAG dependencies.
They remain needed inside those dependencies, so no mathematical nodes or modules are withdrawn.
Both declared proof dependencies are used. The explicit image isomorphism in the old final
DAG step is unnecessary: openness of the representation kernel and its own quotient suffice.

## Where the brief, the DAG or earlier work was wrong

LeanFinder, Loogle, and source grep found no shorter existing theorem asserting the result.
No false statement or definition was found. The theorem's existing docstring records the older
expanded plan; the current DAG has already extracted its topological and algebraic inputs.
The proof follows that extracted route and shortens only the elementary final assembly.
The topology on a finite matrix reduction is explicitly discrete in the input declaration;
its open fibers are used with that topology, without assuming a topology on its coefficient ring.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
