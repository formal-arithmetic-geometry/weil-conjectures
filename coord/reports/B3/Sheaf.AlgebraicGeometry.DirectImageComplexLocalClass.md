## What changed

Replaced the proof hole of `AlgebraicGeometry.directImageComplex_localClass` with the
composition of two calculations: normalized derived direct-image classes on a supplied
integer K-injective model, and the ordinary module/abelian sheafification class of a
nonnegative complex. The existing statement, definitions, public import and docstring
are unchanged. Two proof imports supply the calculations.

Six new modules contain the proved intermediate calculations and private categorical
helpers: `LocalHypercohomologyClassUnit`, `DirectImageResolutionNormalization`,
`DirectImageComplexUnit`, `DirectImageIntegerLocalClass`, `OrdinaryLocalClassCycles`, and
`NonnegativeComplexLocalClass`, all under `Sheaf.AlgebraicGeometry`. The resolution
comparison is derived from the existing universal Leray factorization and naturality;
the ordinary comparison is proved by cancelling the epimorphic cycle projection and
the monic cycle inclusion. No shared definition or existing consumer is changed.

The initially combined file was profiled. Keeping chosen derived functors irreducible
locally and calculating with a supplied resolution reduced repeated unfolding. The
remaining independent calculations were placed in their own modules. Each delivered
file is checked through `lcompile.py`; delivery also runs the required preflight.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.directImageComplex_localClass`.
The six new public theorems are proved:

- `AlgebraicGeometry.localHypercohomology_complexUnit_class`
- `AlgebraicGeometry.directImage_resolution_normalization`
- `AlgebraicGeometry.directImage_complex_unit`
- `AlgebraicGeometry.directImage_integer_localClass`
- `AlgebraicGeometry.ordinaryLocalClass_cycles`
- `AlgebraicGeometry.nonnegativeComplex_localClass`

There are zero remaining or added `sorry` declarations in the delivery. This closes
one hole and adds zero holes; none is split off. The calculations use the existing,
proved section-presheaf and section-cycle APIs.

## No longer needed

No existing module or mathematical dependency is withdrawn. Both original planned
dependencies remain needed transitively through the new calculations. No unit statement
or unit proof step is bypassed. No original public import is removed.

An exploratory import of `Sheaf.CategoryTheory.TotalClassicalResolutionComparison`
was removed: its private naturality calculation is already the public proved source
lemma `Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_hom`, imported from
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact`.
The new helper modules import only the local-model data rather than the larger
`DerivedSquareLocalClassModels` module.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The planned normalization and cycle arguments were
mathematically sufficient, but required explicit naturality, adjunction and
extension-by-zero glue in Lean. The proof retains the exact fixed comparisons rather
than replacing any of their definitions. Degree zero, empty opens and zero complexes
are handled uniformly by the kernel/cokernel and extension identities.

## New nodes

`lem-weil-pbc-local-hypercohomology-complex-unit-class` identifies the local class of the
derived-section unit on an arbitrary integer complex. Its proof normalizes the fixed
sheafification model on a supplied K-injective resolution and uses adjunction-unit
naturality.

`lem-weil-pbc-direct-image-resolution-normalization` identifies the recorded/published
direct-image comparison on any supplied K-injective representative by lifting to the
fixed representative and cancelling the shared image of that lift.

`lem-weil-pbc-direct-image-complex-unit` proves the universal Leray unit equation
on a K-injective complex, before taking homology. The direct-image unit is cancelled
against its inverse recorded resolution comparison.

`lem-weil-pbc-direct-image-integer-local-class` computes the derived local-class/Leray
composite on an integer K-injective complex. The universal Leray unit equation and the
two preceding normalizations give the ordinary sheafification class.

`lem-weil-pbc-ordinary-local-class-cycles` computes that ordinary abelian class on
cycles, using the generic adjoint homology comparison and exact forgetting of modules.

`lem-weil-pbc-nonnegative-complex-local-class` identifies the ordinary module class with
this abelian class after extension by zero and exact evaluation. The existing section
cycle formula identifies the module side; the extension comparisons agree by their
kernel inclusions and their degreewise identity maps.

All six nodes have the original chapter and unit, source references, search records,
verbatim Lean attachments, and complete proof plans. The original node's proof route
is updated to the two actual calculations used by its proof. There is no definition
change record because no existing definition or statement changes.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
