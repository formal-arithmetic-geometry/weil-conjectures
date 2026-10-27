## What changed

Replaced the proof hole in
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationScalar_directImage_mate`
without changing its signature or public imports. Its proof uses a private import of
`Sheaf.Paper.FiniteRealizationRestrictionCube` and a proof import of all declarations of
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` to identify the actual
fixed-scalar restriction mate.

Added `Sheaf.Paper.FiniteRealizationMateAlgebra`, with complete generic proofs of:

- `CategoryTheory.realizationScalar_unit`: the scalar comparison constructed by
  `leftAdjointUniq` preserves the units after conjugating its inverse-realization square;
- `CategoryTheory.scalarTranspose_realization_cube`: a restriction cube and the two unit
  equations imply the scalar-extension transport equation;
- `CategoryTheory.scalarTranspose_inverse_mate`: iterated mates identify the fixed scalar
  transpose with the geometric mate of the inverse scalar comparison.

The forward square `realizationRestrictionFromInverse` is an explicit composite of
realization units, counits and the input inverse square. The new restriction-cube module
constructs `realizationRestrictionRightIso` by exact descent of the existing
`sfInverseRealizationRestriction`, then constructs `realizationRestrictionIso` from it.
The item applies the generic unit lemma to the actual definition of
`realizationScalarIso`, applies the cube-transposition theorem, and identifies the fixed
mate using the actual definitions of `scalarPullbackProEtaleIso` and
`fixedScalarRestrictionDirectImage`.

The remaining geometric step is stated separately in
`Sheaf.Paper.FiniteRealizationRestrictionCube`. It is Step 1 of the original node, has no
scalar-extension functor or scalar adjunction in its statement, and concerns arbitrary
fixed B-coefficient objects. The original node's proof and proof dependencies now record
this decomposition. The unit route through finite-coefficient reduction is preserved.
No existing definition, instance, global attribute, statement or public import is changed.
Local irreducibility of `Functor.mapDerivedCategory` and `Functor.leftAdjoint` keeps
large constructions folded. Local reducibility of the three small equivalence wrappers
exposes their functor/inverse projections. The inverse restriction square uses precisely
the coefficient-map let binding and normalization of the original scalar comparison.
All three modules typechecked together with `lcompile.py --all`; temporary profiling
showed only a few seconds of Lean proof work and was removed before delivery.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationScalar_directImage_mate`
(node `lem-finite-realization-scalar-mate`) by a complete proof from the geometric cube.
The three generic algebra lemmas listed above have complete proofs and no holes.

Added one hole:
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationRestriction_directImage_cube`
(node `lem-finite-realization-restriction-cube`). Its proof is exactly `by sorry`, with
source and the full K-injective-resolution argument in its docstring and node.
There are zero holes left in the item module, zero in the generic algebra module, and
one in the cube module. This is a decomposition: one original hole closed and one
strictly geometric step added, net zero, not an axiom-free proof of the target closure.
No data definition contains a hole or chooses an arbitrary unproved existence witness.

The generic statements apply to arbitrary categories without nonemptiness or exactness
assumptions. The geometric cube was checked on the identity coefficient map, identity
scheme morphism, zero complex, zero coefficient rings and empty schemes: its maps reduce
to the corresponding normalized identities and equivalence triangles. No restriction
functor is assumed to preserve K-injectivity; its restricted complex is separately
resolved, and only the direct image of that resolution arrow is cancelled.

## No longer needed

None. Both original public imports remain necessary for the original statement.
No original declared dependency is pruned from the transitive argument: the restriction
and realization dependencies remain in the geometric cube. No modules are withdrawn.
The generic `normalized_cube` machinery of `DerivedExactSquareCoherence` was examined
but is not imported: applying it would additionally require identifying the specified
comparison maps with all four normalized derived squares.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The equivalence-constructor
projection is reduced using the fully qualified `CategoryTheory.Equivalence.mk`;
unqualified `Equivalence.mk` refers to the relation constructor in these namespaces.
No transparency-respect option is disabled. The original proof has two distinct
steps; the formerly unstated unit/adjunction algebra of Step 2 is now proved in Lean,
while Step 1 is the single explicit remaining obligation. This does not replace the
item by the same scalar-extension compatibility statement under a new name: the new
hole contains none of `realizationScalarIso`, scalar extension, or the scalar mate, and
the proof of their compatibility is the new algebra and its application in the item.

The supplied source comparisons are genuinely normalized comparisons, rather than
arbitrary isomorphisms. Their normalization is essential for the remaining cube.
The existing generic derived-cube theorem does not by itself supply those
identifications. The fixed direct-image comparison has the inverse-mate convention;
the proof accounts for it using `conjugateIsoEquiv` and the inverse scalar pullback mate.

Searches used LeanFinder, Loogle, grep and LeanSearch through the required search tool;
all were successful. They found generic unit, conjugation and iterated-mate identities,
which the algebra proof uses, but no existing theorem for these specified realization
and restriction comparisons. Whole-blueprint searches for realization restriction,
scalar mate and adjunction unit gave no duplicate of the two new nodes.

## New nodes

`lem-finite-realization-mate-algebra` records the explicit forward restriction square
and the three fully proved algebraic identities in
`Sheaf.Paper.FiniteRealizationMateAlgebra`. It realizes the scalar-transposition part of
Step 2 of the item, using Mathlib's unit and iterated-mate identities.

`lem-finite-realization-restriction-cube` records the explicit derived inverse and
forward restriction squares and the remaining geometric cube in
`Sheaf.Paper.FiniteRealizationRestrictionCube`. Its statement is precisely Step 1 of the
item. The docstring and node give the ordinary section square, the two separately chosen
K-injective resolutions, the common invertible direct-image resolution arrow, and the
naturality argument extending the identity to every unbounded object.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
