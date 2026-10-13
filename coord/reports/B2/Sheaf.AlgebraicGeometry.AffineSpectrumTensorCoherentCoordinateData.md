## What changed

Reduced `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_coherent_coordinate_data`
without changing its signature or the definition `ordinaryIsoPullbackStalkComplexIso`.
Added the proof-only import `Sheaf.AlgebraicGeometry.AffineSpectrumTensorGeneratorCoordinates`.
The new module states the geometric ring/input coordinates and the formula on pure tensors
for a fixed, already constructed additive chain isomorphism H.
Its concrete definition `affineSpectrumTensorAdditiveIso` is irreducible to prevent
Lean from repeatedly expanding the nested stalk/complex functor compositions
while lifting component maps. It introduces no new choice or sorry; it composes the
existing canonical isomorphisms. The final coherence proof unfolds it once.

Validation: both modules compiled together without warnings; the main module
finished in 42.2 seconds and the generator module in 24.6 seconds in the profiling
run. The delivery dry run checks the final files and their axiom/declaration records.

The completed argument proves scalar compatibility by tensor induction: on d tensor x,
H(r d tensor x) = eD(r d) tensor q(x) = eD(r) times H(d tensor x).
It lifts each component with ModuleCat.isoMk, assembles the components using
HomologicalComplex.Hom.isoOfComponents, and obtains the requested coherence by
cancelling the inverse spectrum tensorStalkIso in H. The inverse of the linear
comparison is supplied by the existing additive component isomorphisms, rather
than chosen from a new existence hole. A proved private helper `tensor_additive_smul`
handles the tensor induction for general scalar-extension modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_coherent_coordinate_data`
(node `lem-pc-affine-spectrum-tensor-coherent-coordinate-data`). No sorry remains
in the item's module.

Added one hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_generator_coordinates`
(node `lem-pc-affine-spectrum-tensor-generator-coordinates`, new module
`Sheaf.AlgebraicGeometry.AffineSpectrumTensorGeneratorCoordinates`).

This is a decomposition: one original hole closed, one strictly smaller geometric
hole added, net zero holes closed. The new statement supplies no tensor chain map,
no D-linearity, no inverse for such a map, and no chain-map coherence equation.
Those are constructed and proved in the delivered module.

## No longer needed

No existing imports, nodes, or modules are pruned. Both original public imports
are required by the original signatures and definitions. In the parent node's
proof dependencies, the definition-only nodes `def-pc-scheme` and
`def-pc-derived-category` move to the sublemma's statement dependencies; they
remain required by its statements. The separate balanced tensor-map construction
and inverse construction described in the old proof are unnecessary: the existing
additive isomorphism provides both maps after scalar compatibility is proved.
The original unit's realized statement/steps are empty and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's dependency declarations provide the stalk comparison and composition
mate, but do not themselves state the ring/input coordinates with their generator
formula. That geometric calculation is the remaining sublemma. The parent node's
proof plan has been updated to the actual tensor-induction/linear-lift argument.

The blueprint ancestor lookup for this item returns None: its created.item chain
uses Lean module names rather than node ids. The new node records a null ancestor,
its parent node in via, and the exact parent proof step it serves. Blueprint searches
for 0098, affine spectrum, and tensor/stalk terminology found no duplicate blueprint
statement. Repository searches found no existing statement of the generator formula.
LeanFinder returned only scheme pullback tensor-congruence lemmas; Loogle found
TensorProduct.induction_on; Mathlib grep found stalkPullback/germ_stalkPullbackHom
components. LeanSearch was unavailable with HTTP Internal Server Error, recorded
as unavailable rather than as a negative search.

Source reading: Stacks Tags 0098 (stalk pullback), 0096 (pullback adjunction), and
0DJ8 (affine reduction) were read on the Stacks site and in sheaves.tex/perfect.tex downloaded
into sandbox scratch. Their labels are lemma-stalk-pullback-modules,
lemma-adjoint-pullback-pushforward-modules, and
lemma-single-complex-base-change-condition. This machine's clone contains the
literature index but not the downloaded source tree. The new statement
is the generator calculation underlying these constructions, not an assertion
that the tags directly state this exact Lean theorem. Edge cases: zero complexes,
unbounded complexes, and arbitrary affine stalk rings require no flatness or
nonvanishing assumption; all equalities are termwise. For the identity spectrum
square the coordinate isomorphisms may be identities and the formula is the
identity tensor formula. For an empty scheme there is no z0, so the statement
has no instance to check; no nonempty-scheme hypothesis has been introduced.

## New nodes

`lem-pc-affine-spectrum-tensor-generator-coordinates`:
`dag/nodes/sec-picard-framework/lem-pc-affine-spectrum-tensor-generator-coordinates.json`,
Lean module `Sheaf.AlgebraicGeometry.AffineSpectrumTensorGeneratorCoordinates`.
It isolates the ring and input-complex coordinate construction and the formula
for the canonical additive comparison on pure tensors. Its proof is documented
step by step, and its searches are recorded in searches.jsonl. No interface change,
forced adaptation, or change record is needed. The first dry run flagged a local
omit command at the private helper as an interface command; the helper was moved
before the section variable and the omit command removed. The delivery tool has
an explicit worker-dry-run exception for the second-reading section when it is
the only pending check; that section remains for the second reader.

## Second reading by B2

1. I compared the delivered parent module with the repository version. The theorem and definition signatures are unchanged; the only interface change is the declared proof-only import and the separately documented new node. Verdict: pass.

2. I compiled both delivered modules with `lcompile.py --all`. There are no errors, warnings, forbidden declarations, or sorry terms in the parent module. The generator-coordinate theorem is the one named split-off sorry, with its matching node and proof docstring. Verdict: pass.

3. I checked the generator-coordinate statement against its edge cases and dependencies. It asserts only the ring coordinates, the input-complex isomorphism, and the pure-tensor formula; it does not restate the parent chain-isomorphism or coherence conclusion. The statement is needed by the parent proof and no duplicate declaration was found in the repository or Mathlib searches. Verdict: pass.

4. I followed the proof from the target downward. The parent proof uses the new generator lemma, tensor induction, component linear lifts, and inverse cancellation. The imports retained are used, and the unit route is preserved; no additional pruning is available. Verdict: pass.

5. I checked the parent and new DAG records against the Lean declarations. Their proof steps, proof dependencies, origins, module records, and split status agree with the delivered code; the new node records the decomposition and its source. Verdict: pass.

Changed after this reading: appended this review section only. No Lean code or node content required repair.
