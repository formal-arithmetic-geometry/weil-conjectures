## What changed

Replaced the sole hole in
`AlgebraicGeometry.exists_marked_curve_diagram_model` with a complete Lean assembly
proof, keeping its statement and public imports unchanged. Added proof-only imports
of `Sheaf.AlgebraicGeometry.UnmarkedCurveDiagramModel` and
`Sheaf.AlgebraicGeometry.FiniteClosedImmersionLocus`.

The assembly first descends the unmarked diagram, retaining the cartesian comparison
for its finite surjection. A separate finite-morphism locus theorem produces the
marked thickening open. For each point of a constant-field model above η, universal
injectivity identifies its image in the cover, and the cartesian field square
supplies its unique generic preimage. A point in the given dense marked open maps
to that point by the supplied compatibility equations and the singleton spectrum
of the field. These pointwise steps are proved in Lean, including the coproduct
comparison. No marked-open descent or further shrinking is used.

The two remaining obligations are separate mathematical parts of the argument.
The unmarked theorem has no marked-open hypothesis or conclusion; it records the
cartesian finite comparison required to apply the locus theorem. The locus theorem
concerns arbitrary finite maps and arbitrary base changes, with no curves, generic
points or diagram-descent data. Its finite-cokernel proof is detailed in its
docstring and node. Neither theorem restates the assigned marked theorem.

Validation: all three modules compiled cleanly through lcompile.py after removal
of the unused Thickening import from the new unmarked module (4.0, 5.6 and 9.0 s).
No existing signatures, definitions, source-library declarations or consumers
were changed. The unit's proper-base-change route is retained.

## Proved and sorry left

Closed the original hole:

- `AlgebraicGeometry.exists_marked_curve_diagram_model`
  (`lem-weil-pbc-marked-curve-diagram-model`). Its proof now compiles from the two
  named statements below; there are zero holes in the item module.

Added two named holes, each in its own new module:

- `AlgebraicGeometry.exists_unmarked_curve_diagram_model`
  (`lem-weil-pbc-unmarked-curve-diagram-model`): unmarked finite-diagram descent,
  preserving the comparison squares and the generic geometric fibre properties.
- `AlgebraicGeometry.exists_finite_closedImmersion_locus`
  (`lem-weil-pbc-finite-closed-immersion-locus`): the finite-cokernel support argument
  constructing the maximal open where a finite map is a closed immersion and
  containing every closed-immersion locus after base change.

This is a decomposition: one original hole closed, two holes added, two holes left
in the packet, net one additional hole before any closure-ledger adjustments.
It is not a proof free of sorry dependencies. No hole occurs inside a definition.

## No longer needed

No existing public import was removed. The unused copied import
`WeilConjectures.AlgebraicGeometry.Thickening` was removed from the new
`UnmarkedCurveDiagramModel` module. The item has exactly the two proof-only imports
used by its assembly.

The original marked-open descent route is replaced by the finite closed-immersion
locus construction. Consequently these old plan dependencies are absent from the
new route, including its unmarked child:

- `pqf-lem-limit-qc-open-descends`: we do not descend W₀ or choose a quasi-compact
  model for it.
- `lem-weil-pbc-descend-closed-immersion`: we do not shrink a base to descend the
  closed-immersion property; the support complement gives an open directly.
- `lem-weil-pbc-scheme-over-limit`: its former separate marked-open approximation
  invocation is unnecessary; the retained finite-family object/arrow/equality
  descent interfaces provide the unmarked model.

The other diagram-descent dependencies remain under the new unmarked node. The
thickening definition and surjectivity under base change remain direct assembly
dependencies. No module is withdrawn, and no claim is made that a source-library
module with other consumers can be removed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false, and the assigned theorem is unchanged. The former
plan descended the marked open and then its closed-immersion restriction. Finiteness
of ν permits a shorter marking argument: take the complement of the support of
coker(O_X → ν_*O_Y). This cokernel is finite type, so its support is closed and
commutes with arbitrary base change. Thus W₀ is contained in the generic inverse
image of this open without needing equality of opens or another shrinking.

The extra cartesian comparison for ν is necessary: the old item supplied component
squares but did not expose such a square for its finite map. The new unmarked step
explicitly retains it from the descended diagram, using universality of finite
coproducts. The marked-point conclusion is then a real assembly argument, rather
than another unproved marked-diagram statement.

Edge cases checked in the arguments: the finite-locus statement allows empty W₀,
empty source or target, nonreduced bases, and arbitrary nonflat base change;
Nakayama uses finite generation, not Noetherianity. For the item, density in each
nonempty A_i gives the point used in the image proof. If n=0 all component and
marked-image assertions are vacuous. No arbitrary data witness is chosen in a
new definition.

## New nodes

`lem-weil-pbc-unmarked-curve-diagram-model` is the unmarked descent paragraph of
Stacks Tag 0GK7, split before the marking paragraph. It retains the finite diagram,
its cartesian comparison maps, and geometric generic fibres; it constructs no
marked open. Its statement, full proof in words and Lean attachment are recorded
in the new node and module.

`lem-weil-pbc-finite-closed-immersion-locus` is the general finite-cokernel step used
for the marking paragraph. Its source is the affine criterion for closed immersions
and the support and pullback theorem for finite type modules (Morphisms 056J).
The node gives the finite pushforward, cokernel, support-complement and base-change
steps; the docstring also spells out the residue-field/Nakayama argument. Searches
found no matching library declaration. No change record is needed because no
existing statement or definition was changed.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
