## What changed

The statement of `AlgebraicGeometry.exists_eventual_immersion_vanishingSections`
is unchanged. Its proof now constructs the actual kernel submodule, chooses a finite
basis, constructs the compatible restricted sections, proves the span and linear
independence assertions, and proves that those restricted sections generate.
The degree bound is `a + r`, where `a` is the ideal-twist generation bound and `r`
is one fixed positive very ample power. Generation is used in degrees `n` and `n-r`.

The new module `Sheaf.DeligneLaumon.BertiniImmersionAux` isolates the product-system
immersion criterion from the final paragraphs of Stacks Tag 0FD5. It assumes an
already specified generating system, an explicitly supplied globally generated
ideal twist, and one fixed very ample power. It requires neither properness nor
ampleness and asserts neither eventual existence nor any basis construction.
The main proof supplies all its hypotheses. This is a decomposition, not a claim
that the geometric chart argument has been proved.

The kernel is a real `Submodule` defined by zero pullback, not an object selected
from an unproved existence theorem. All private helpers are proved. The proof
compares the tensor-pullback adjunction with the standard pullback adjunction
before invoking the existing closed-immersion ideal-tensor sections theorem.
No existing definition, theorem signature, or target statement was changed.
The removed public imports and local proof commands are recorded in
`coord/changes/bertini-sections-proof-imports.md`.

Both delivered modules compiled together in import order. The main module compiled
in 11.3 seconds against the current source-root dependency after caching its repeated sheafification and local-bijectivity
instances; the unchanged direct consumer `WeilConjectures.AlgebraicGeometry.Bertini`
compiled against the sandbox overlay in 1.9 seconds. Earlier incremental checks
also verified the basis factorization, ideal restriction, and generation argument. The first completed dry
run rejected only the missing change record; that record is now supplied, and
the latest corrected dry run passed for commit `7b408734f4`, classified CODEX for
independent review. Both module compiles and axiom probes passed.

## Proved and sorry left

Closed the original whole-proof hole in
`AlgebraicGeometry.exists_eventual_immersion_vanishingSections`
(node `lem-zl-bertini-sections`) by a complete Lean proof from the library and the
separate criterion below. The assigned module now contains zero `sorry`.

Added one whole-proof hole:
`AlgebraicGeometry.vanishing_linear_system_isImmersion`
(node `lem-zl-bertini-product-system-immersion`, module
`Sheaf.DeligneLaumon.BertiniImmersionAux`). Its docstring and node give the complete
product-section chart proof. Thus one original hole is closed and one hole is
split off: net zero, a decomposition. There are no other delivered holes and no
holes in definitions or private declarations.

The new criterion was checked mathematically for an empty source, an empty
complement (`Z=Y`), an empty closed subscheme, zero-dimensional projective spaces,
`r=0`, and `n=r`. The degree inequality is explicit and the scalar action is the
canonical action through the structure morphism. There is no smoothness,
reducedness, perfectness, infinite-field, or nonempty-index assumption. In the
empty-complement case the image-cover argument is vacuous. For `n=r`, the ideal
generation hypothesis is in degree zero, as required by the product argument.

## No longer needed

Removed these direct imports from the assigned module:

- `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`
- `Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `WeilConjectures.AlgebraicGeometry.Ample`
- `WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration`
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible`

The remaining statement imports are public; the five added proof imports are
ordinary imports. The relative ample predicate already supplies the exact Serre
A theorem in `Modules.HilbertPolynomial`; the original conversion through
`lem-weil-pbc-projective-ample-invertible` and
`def-weil-pbc-ample-invertible-module` is not needed in the main argument.
Likewise the explicit passage through `pqf-lem-coherent-ft-locnoeth` is replaced
by the existing ideal finite-presentation API. These are removed as direct proof
dependencies, not asserted absent from every transitive library dependency.

The original chart, fibre, tensor, affine-map, permanence, cancellation, and
image-locality nodes are still needed for the new criterion's proof plan; they
are not claimed pruned. Basis-change projective automorphisms are unnecessary
for the proved assembly. No module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

During this long-running item the ideal-tensor theorem moved from
`Sheaf.AlgebraicGeometry.ClosedImmersionIdealTensorSections` to the proved module
`WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections`. The fresh
dry run detected the stale source import; it is now updated to the current module.
A preliminary auxiliary signature in the interrupted scratch work omitted the
necessary degree `n-r` product hypothesis. It was replaced before delivery with
the true criterion stated here. It has never been delivered or imported by any
other item.

The original DAG's relative-to-absolute ampleness conversion is unnecessary:
the proved relative Serre generation theorem accepts the existing `IsAmple`
hypothesis directly. The fixed-very-ample-power route and the unit route are
preserved. The source's `s_1 in V_1` is the known degree typo; the Lean argument
uses a generator in degree `n-r`, never degree one.

Compile-server transport failures and later temporary provider interruptions
were checked before resuming. They did not initiate a delivery. The completed
compile results were read before rerunning changed files. No launcher script
or budget metadata was edited.

## New nodes

`lem-zl-bertini-product-system-immersion` records the genuine geometric portion
of Tag 0FD5: a fixed very ample system multiplied by generators of an ideal
twist, and included in a specified linear system, forces the latter map to be
an immersion on the complement. The node has its own Lean module, source,
complete chart proof plan, four recorded search methods, and edge-case checks
above. Its hypotheses are the finite-degree inputs proved by the main module;
it is strictly smaller than the original eventual existence theorem.

Change record: `coord/changes/bertini-sections-proof-imports.md`.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
