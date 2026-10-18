## What changed

Proved `DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology` in
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`, with its statement,
universes, visibility, and definitions unchanged. All four steps of the existing
DAG proof are realized directly, so no node edits or new nodes are needed.

Forwards, use the finite-free representative's upper support bound, then apply
`Module.Finite.of_injective` to its cycles, finite generation of a quotient to its
homology, and the homology functor's comparison and isomorphism to transport the
result. This is the Noetherian-submodule argument in steps 1 and 2.

Backwards, apply `Module.exists_finite_free_resolution` to each finite cohomology
module. Lift the finite function modules using `ULift.moduleEquiv` into the required
universe, construct a chain complex, and verify exactness and surjectivity of its
augmentation directly from the resolution's kernel-image equalities. Package this
as a projective resolution and extend it to a cochain complex by Mathlib's
`ProjectiveResolution.cochainComplex`. The extension is zero above zero; below zero
its terms are isomorphic to the original finite free modules. The augmentation is
a quasi-isomorphism and hence gives the required derived isomorphism. Finish with
the existing `DerivedCategory.isPseudoCoherent_of_homology` declaration, as step 4
requires. No data is chosen from an unproved existence theorem: the finite-free
resolution theorem is proved in the existing library.

Added proof-only imports `Mathlib.Algebra.Category.ModuleCat.Projective` and
`Mathlib.CategoryTheory.Abelian.Projective.Extend`. All original imports remain.
The proof follows Stacks Tag 066E (2) and its finite-free-resolution argument, as
specified in the theorem docstring. Zero modules and zero-rank free terms are
covered by the same construction; no lower cohomological bound is used.

The completed file compiles through `lcompile.py` in approximately six seconds.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`
(node `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion`).

No `sorry` remains in the item module. No holes were added or split off.

The proof uses the existing, still unproved declaration
`DerivedCategory.isPseudoCoherent_of_homology`
(node `lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent`, module
`Sheaf.RingTheory.PseudoCoherentOfCohomology`). Thus the delivered theorem's
transitive axiom check still reports `sorryAx`, alongside `propext`,
`Classical.choice`, and `Quot.sound`; this delivery does not claim closure of that
existing dependency. The imported finite-free resolution theorem is already proved.

## No longer needed

None. No original import, planned dependency, node, or module is pruned.
The existing route and the unit's realized steps are retained. A redundant trial
import of `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` was omitted because
`RingPseudoCoherent` already publicly imports it through `ModuleCat.Free`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The natural-language packaging step
requires universe lifting of the finite function modules because the item uses
`ModuleCat.{max u v} R`; this is handled explicitly without changing a signature.
No definition repairs, consumer adaptations, change records, or new nodes.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
