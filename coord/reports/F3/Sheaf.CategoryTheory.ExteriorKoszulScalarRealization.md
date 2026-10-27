## What changed

The statement of `CategoryTheory.exteriorKoszul_scalar_realization` is unchanged.
Its proof now constructs a coefficient ring homomorphism into the endomorphisms
of the regular sheaf by conjugating the images of multiplication through `c`.
This obtains every polynomial scalar identity from the given hypothesis; no
ring-homomorphism assumption on `s` is added.

The item proves that the actual increasing-wedge inclusions of each extended
exterior term form a finite coproduct, including the unsupported positive degrees,
and proves the action of an arbitrary diagonal on every ordered wedge. Additivity
preserves that finite coproduct. Uniqueness of the coproduct comparison then
constructs degreewise isomorphisms to the normalized dual-tower coordinates.
The proof assembles the chain isomorphisms by comparing differential matrices,
proves naturality for every supplied `n <= m` transition, and verifies the exact
empty-subset normalization using `exteriorPower.zeroEquiv`.

The algebraic coordinate module constructs the actual dual-basis projections
and measures the entries of the constructed contraction differential with them.
It proves its finite matrix expansion from the basis identity. Its definitions
contain the actual boundary map, with no asserted sign formula supplying data.

One new theorem remains for the finite basis and matrices of the ringed dual.
It has no realization functor, regular-module comparison or supplied transition
family. The original theorem's entire transfer through an arbitrary additive
functor is proved from this finite matrix calculation.

The required searches used leanfinder, Loogle and Mathlib grep. Existing project
comparisons and both declared proof dependencies were read. The existing
exterior-to-tensor comparison is restricted to a successor coefficient universe;
it does not apply to the arbitrary universe in this statement. The actual
ringed negative-to-dual comparison is now proved, but it does not itself state
the normalized differential and all-transition coordinate matrices.

## Proved and sorry left

The original hole in `CategoryTheory.exteriorKoszul_scalar_realization` is closed
by a complete Lean combination of the proved algebraic coordinate expansion
and one strictly smaller ringed-coordinate statement. This is a decomposition,
not an independent proof: one upper hole is closed, one lower hole is added,
and no `sorry` remains in the item itself or the algebraic coordinate module.

The new theorem `CategoryTheory.exteriorKoszulBasis_d` is proved by the finite
basis identity. The delivery leaves exactly one named theorem hole:

- `CategoryTheory.exists_ringedKoszulDualBasis`, node
  `lem-sfb-ringed-koszul-dual-basis`, in
  `Sheaf.CategoryTheory.RingedKoszulDualBasis`.

All private helpers in the item are proved. All new data definitions are explicit
constructions; no definition chooses data from a holed existence theorem.
All three delivery modules compiled together in import order without errors
or warnings: `ExteriorKoszulBasisDifferential` in 3.1 s,
`RingedKoszulDualBasis` in 6.7 s, and `ExteriorKoszulScalarRealization` in
15.3 s. A direct comparison confirmed the original theorem signature is
unchanged; all node attachments and dependency references were checked.

## No longer needed

No existing public import is removed, and no module is withdrawn or globally
pruned. No chapter or unit route is changed.

The item no longer needs direct proof imports of
`Sheaf.CategoryTheory.SignedKoszulFiniteCoordinates` or
`Sheaf.CategoryTheory.RingedNegativeKoszulDuality`: their finite tensor and duality
arguments are dependencies of the new ringed-coordinate node. They remain needed
there and are not claimed as pruned.

`Sheaf.Paper.WeilExteriorKoszulTensorComparison`,
`Sheaf.Paper.WeilNegativeKoszulTensorRealization`, and
`Sheaf.Paper.WeilNegativeKoszulFactorRealization` are not imported: the finite
basis construction works in the original arbitrary universe and uses only
additivity, without a monoidal structure on the realization functor. These are
alternative tools not used by this proof, not withdrawn modules.

## Where the brief, the DAG or earlier work was wrong

The declared finite-coordinate dependency describes `K tensor N` and its
existentially supplied negative transitions. The duality dependency identifies
the actual negative transitions with the dual ones. Neither declaration directly
states the required actual exterior/dual matrix identification or the matrix
for every actual dual-tower transition. The remaining ringed-coordinate node
makes this missing finite identification explicit; the functorial, coproduct,
diagonal and unit glue is proved in the item.

No mathematical error in the item statement was found. In particular, the
argument allows the empty list, zero rings, empty sites, and zero or unit
coefficients. The source coproduct proof treats positive degrees as zero objects;
its supported-degree basis proof imposes no nontriviality assumption.

## New nodes

`lem-sfb-exterior-koszul-basis-differential` records the proved finite coordinate
expansion of the actual constructed exterior boundary. It defines real basis
inclusions, their dual projections and the measured matrix entries. The proof
uses the finite basis identity and the linear endomorphisms of A, including
unsupported integer degrees and zero rings.

`lem-sfb-ringed-koszul-dual-basis` states only the finite subset basis and the
differential, actual transition, and empty-unit matrices on the ringed side.
Its differential entries use the measured algebraic boundary coefficients.
Its proof plan uses the existing finite tensor coordinates and proved negative
duality, with induction for all transitions; its source is Stacks Tags 0664 and
0A0E. The condition on the coefficient endomorphism homomorphism is stated
explicitly. There are no changes to other existing modules and no change record
is required.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
