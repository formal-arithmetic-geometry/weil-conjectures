## What changed

Decomposed `WeilConjectures.StratifiedContinuousLattices.continuous_constructible_stratified_lattices`
into four independent parts of its original seven-step argument. Its signature and every
original data declaration are unchanged. The final Lean proof chooses the uniquely
normalized coefficient families, obtains their coefficient geometry, and constructs
`Family` using those fields, the ordinary scalar comparison and the stratified lattice theorem.

Moved the original interfaces, verbatim, into `Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData`
and publicly reexported them from the original module. This is necessary to place each
remaining theorem in a new module without a cycle. All original public imports remain
available through the reexport. The new `CoefficientGeometry` structure contains only
the original coefficient restriction/change and coherence fields; it has no lattice or
constructibility clause.

The six sandbox Lean modules compiled together successfully on the first complete pass.
The interface declaration block was also compared byte-for-byte with its original and
is identical. The scalar comparison is undergoing a further direct adjunction proof attempt.

## Proved and sorry left

Decomposition, not a completed mathematical proof: the one original hole in
`WeilConjectures.StratifiedContinuousLattices.continuous_constructible_stratified_lattices`
is replaced by a complete constructor proof. Four strictly smaller holes are split off:

- `WeilConjectures.StratifiedContinuousLattices.ordinary_section_scalar_comparison`
  (`lem-zl-ordinary-section-scalar-comparison`): general ordinary scalar comparison only.
- `WeilConjectures.StratifiedContinuousLattices.normalized_continuous_coefficient_family`
  (`lem-zl-normalized-continuous-coefficient-family`): coefficients/encodings at one field only.
- `WeilConjectures.StratifiedContinuousLattices.continuous_coefficient_geometric_coherence`
  (`lem-zl-continuous-coefficient-geometric-coherence`): restriction and coefficient change only,
  parameterized by already supplied normalized coefficient data.
- `WeilConjectures.StratifiedContinuousLattices.normalized_stratified_embedded_lattices`
  (`lem-zl-normalized-stratified-embedded-lattices`): embedded lattice refinement only,
  at one field and for one supplied coefficient family, module and lisse partition.

No sorry remains in the original item or in the extracted data module. No definition
contains a sorry. Each new hole is a public named theorem in its own module, with the
source and complete proof in words in its docstring and node. The first-pass hole count
is 1 closed by decomposition, 4 added, net -3. This does not claim a net proof gain.
The complete Family assertion is not restated as a new hole.

## No longer needed

The final constructor proof privately imports exactly the four component modules.
These former private proof imports are removed from the item:

- `Sheaf.Paper.EmbeddedLatticeCoefficientComparison`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
- `Sheaf.Paper.ContinuousChartSchemeNaturality`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback`
- `Sheaf.Paper.ContinuousModuleEncodingScalarExtension`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `Sheaf.Paper.ContinuousModuleEncodingLocalFreeness`
- `Sheaf.Paper.StratifiedLattice`
- `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`

Their mathematical uses remain in the component nodes' proof plans. No listed source
lemma, blueprint unit, module or DAG node is asserted globally unnecessary, and no
source-library declaration is removed. The parent's four new direct dependencies replace
its old direct proof-dependency list, with the old dependencies retained below the
appropriate components. The original unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original seven-step argument is mathematically consistent, but its existing Lean
dependencies do not directly supply the normalized `Family` fields. In particular:
continuousModuleEncoding_scalar_extension is Type-0 and an objectwise isomorphism without
the pure-tensor normalization; continuousRing_locallyFree_iff is Type-0 while this item
uses arbitrary coefficient universes; continuousChart_scheme_naturality is also stated
for Type-0 coefficients. Transport through the published universe-polymorphic encodings
and the actual inverse-image/scalar adjunction units remains real proof work.

The fixed-field internal lattice theorem is also Type-0 with the spectral norm, whereas
this item uses Type-u fields with any extending norm. Norm uniqueness and a coefficient
universe transport are needed before applying that theorem. The new lattice theorem
records this proper part of the argument rather than assuming the entire final result.

The sources were read at BS 6.8.2, 6.8.3, 6.8.4(6), 6.8.13 first paragraph and 6.8.15,
and Stacks 03EK/03EL. Edge cases checked: empty schemes and partitions, rank zero,
locally varying rank, nonreduced domains and ramified field embeddings with compatible
ideal powers. No statement was weakened. There are no forced adaptations.

## New nodes

`def-zl-continuous-constructible-lattice-data` attaches the unchanged extracted interfaces.
Its main declaration is `Family`; every moved declaration is included in its Lean record.

`lem-zl-ordinary-section-scalar-comparison` isolates original step 4 for arbitrary internal
commutative coefficients, retaining the formula on every pure tensor.

`lem-zl-normalized-continuous-coefficient-family` isolates steps 2, 4 and 5 at one field,
without choosing any lattice or stratification.

`lem-zl-continuous-coefficient-geometric-coherence` isolates step 3 for already supplied
normalized charts, with restrictions and field changes chosen together to keep coherence.

`lem-zl-normalized-stratified-embedded-lattices` isolates steps 1, 6 and 7 at fixed
coefficients and a given lisse-partition witness, including reduction and further pullback.

Change record: `coord/changes/A3-continuous-constructible-lattice-interface-extraction.md`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
