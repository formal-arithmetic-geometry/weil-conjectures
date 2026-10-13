## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.picardExternalCup_right_cech_diagram`
without changing its statement or existing docstring. The main proof chooses finite
subcovers of the affine covers, combines two independent fixed-model lemmas, and
proves all four negative homology vanishings using zero extension and Mathlib's
`isZero_homology_of_isZero_X₂`.

Added `PicardExternalRightCechModels`: explicit scalar Cech, tensor-total Cech and
product-cover Cech coefficient functors, assembled from existing library functors.
All data is constructed, and the three zero-map instances are proved. This fixes
the complexes that the remaining lemmas discuss, rather than selecting arbitrary
complexes from a holed existence theorem. Added proof-only imports of
`PicardExternalRightCechExact` and `PicardExternalRightCechComparison` to the item.

The entire four-module sandbox compiles. No existing interface, target, definition,
universe or visibility changed. No other group's module was adapted.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCup_right_cech_diagram`
(lem-sc-picard-external-cup-right-cech-diagram).

Added two holes, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_exact`
  (lem-sc-picard-external-right-cech-exact): short exactness of the two **fixed**
  functorially constructed Cech sequences. It makes no cup comparison assertion,
  needs no cover condition and constructs no homology isomorphisms.
- `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_comparison`
  (lem-sc-picard-external-right-cech-comparison): refinement/cup morphism and scalar
  homology comparisons for the **fixed** sequences. It needs no short exactness
  hypothesis and asserts neither exactness nor negative vanishing.

This is a decomposition (one hole closed, two added), not a complete geometric
proof. No sorry remains in the item. Negative vanishing, cover selection and
assembly of the witnesses are proved. The models module has no sorry.

## No longer needed

Removed redundant direct imports from new modules: `Mathlib.Algebra.Homology.Embedding.Extend`
from the models, and `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`
from the two lemma modules; these are already supplied by the public import closure.

No original import was removed: the three public imports support the unchanged
statement. No existing module is claimed globally unreachable.

`lem-weil-pbc-derived-functor-long-exact` and its module
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` are not required
on this route. Degreewise affine section exactness suffices; no full derived
long exact sequence is needed to construct this diagram. It is removed from the
item's proof dependencies and is absent from both new lemmas' plans.

The other twelve old proof dependencies are retained where applicable in the two
new nodes. They are now responsibilities of those next items, rather than direct
steps left implicit in this theorem. `lem-sc-picard-kunneth-resolution-model` is
also available through the existing public cochain import.

## Where the brief, the DAG or earlier work was wrong

The old DAG describes a valid geometric argument, but its one large step hides
the assembly of scalar Cech functors, exactness on product intersections and the
simultaneous homology comparisons. The listed declarations are not a theorem
constructing that diagram. The two new nodes separate its exactness and comparison
parts, and the definitions expose the actual Cech complexes needed by both.

The local `literature/stacks-project/varieties.tex` is absent. The official Stacks
Tag 0BED page was read, including equation the project server, coefficient sequence
functoriality and the same argument in the second variable. LeanSearch returned
Internal Server Error; LeanFinder, Loogle and local/source/Mathlib grep were used.
No departure from the theorem-of-cube unit's route is made.

Edge cases checked mathematically before stating the new lemmas: empty finite
families give zero Cech terms; a cover of an empty scheme gives the zero complexes;
zero coefficients give zero tensor/product terms; degree zero uses the usual
Cech equalizer and normalization; negative terms vanish by actual zero extension.
Exactness does not assume O_X-flatness of F: tensor exactness takes place over k
on the affine factor section modules. The comparison is independent of exactness.

## New nodes

`def-sc-picard-external-right-cech-models` (module
`Sheaf.AlgebraicGeometry.PicardExternalRightCechModels`) packages existing scalar
restriction, ordered Cech, tensor total, tensor pullback and zero extension as
coefficient functors. It also records their proved zero-map instances. No data
is selected from an unproved theorem. The existing `cechOver` construction is a
single coefficient complex, not either of these right-variable diagram functors.

`lem-sc-picard-external-right-cech-exact` (module
`Sheaf.AlgebraicGeometry.PicardExternalRightCechExact`) isolates exactness of the
fixed tensor and product Cech sequences. Its source is Tag 0BED's short exact
coefficient paragraph and the affine pullback/tensor formulas. The complete proof
in words is in its docstring and DAG steps.

`lem-sc-picard-external-right-cech-comparison` (module
`Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison`) isolates refinement,
signed cup and the natural scalar-model homology identifications on the same
fixed complexes. Its source is Tag 0BED, equation-kunneth-on-cech, with Tags 01FD,
07MB and 0FKV for comparison with pullback and cup. The complete proof in words
is in its docstring and DAG steps. No cup invertibility is used.

All three nodes record LeanSearch unavailability, LeanFinder/Loogle results,
Mathlib/source/project grep and the absence of a matching imported blueprint node.
No change record is necessary: all existing interfaces remain identical.

## Second reading by M4

1. Interface check: PASS. Diffed the item against the repository: the existing
   theorem signature and docstring are byte for byte unchanged. Only two plain
   proof imports and its proof body changed. All three additional modules and
   their declarations are new. No target or existing definition changed; no
   forced adaptation or change record is needed.
2. Proof check: PASS as a decomposition. Compiled all four modules in import
   order, without errors or warnings. Inspected every declaration and the two
   whole-theorem sorries. Scratch `#print axioms` checks show only propext,
   Classical.choice and Quot.sound for the three model definitions and three
   zero-map instances. The item and the two split theorems additionally use
   sorryAx, exactly as expected from the reported open geometric lemmas.
   There is no hollow definition or forbidden declaration. The adjunction
   choice in the zero-map proof supplies only an additive property of an
   already constructed functor, not coefficient or complex data.
3. Split check: PASS. Read the exactness and comparison statements against their
   fixed functor definitions and Stacks Tag 0BED, equation the project server and its
   coefficient diagram (https://stacks.math.columbia.edu/tag/0BED). Exactness
   requires no covering hypothesis; comparison requires no exactness hypothesis.
   Neither is a renamed copy of the item, and both are strict parts of its
   argument. Finite families have finitely many tuples in each degree;
   totalization has finitely many summands. Empty index families yield zero
   terms; an empty covering family in the comparison forces the corresponding
   scheme empty. Empty opens, zero coefficients, degree zero and nonflat F over
   O_X cause no counterexample: the exact tensor operation is over the field k.
   Repeated LeanFinder searches using affine section exactness, flat tensor and
   coefficient naturality found useful generic tools, including
   Module.Flat.lTensor_shortComplex_exact, but no matching full lemma. Read the
   upstream abelian-valued shortExact_cechComplex and the opposite-variable
   LeftComparisonComplexes theorem; neither closes these fixed scalar-model
   statements directly. Neither remaining hole admits a few-minute closure.
4. Route and pruning check: PASS. The assembly proves finite-cover selection
   and all four negative homology vanishings explicitly. Public imports in new
   files support definitions or statements; proof imports are plain. Removed
   the unnecessarily broad PicardExternalCupCochain import from Models, using
   FieldLinearModuleCohomologyOperations and Mathlib.Algebra.Homology.Bifunctor
   instead; Comparison now imports PicardExternalCupCochain explicitly because
   its signature needs it. The unit record is unchanged: its current realized
   fields are empty (statement [], steps [[]]); this pre-existing bookkeeping
   gap is not a license to bypass the theorem-of-cube route. The same finite
   affine-cover/cup route is preserved.
5. DAG check: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Its direct dependencies are exactly the model definitions,
   exactness and comparison lemmas used by Lean. The three new nodes have
   source, docstring proof, search records, provenance, unit and chapter fields.
   Normalized their lean.statement fields to the literal multiline signatures.
   The old derived-functor long-exact dependency is removed; the twelve other
   old dependencies remain transitively assigned to the two split plans.

Second-reading changes: narrower model imports and explicit comparison import;
literal new-node Lean signatures; this review and the pruning clarification
below. No proof body or statement needed repair.

Pruning clarification: all thirteen original direct proof dependencies were
replaced on the item node. The twelve listed below remain transitive geometric
responsibilities of Exact or Comparison, so their modules are not claimed pruned:
lem-sc-cech-comparison-map-iso-affine,
lem-sc-cech-comparison-map-naturality, lem-sc-cech-comparison-natural,
lem-sc-picard-affine-diagonal-intersections,
lem-sc-picard-cech-cup-pullback-compat, lem-sc-picard-external-cup-cochain,
lem-sc-picard-kunneth-resolution-model, lem-sc-qcoh-cech-total-tensor-nat-iso,
lem-weil-pbc-fibre-product-affine-spectra,
lem-weil-pbc-module-pullback-affine-sections,
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections,
pqf-lem-affine-vanishing. Only
lem-weil-pbc-derived-functor-long-exact is unused on the replacement route.
The models no longer import PicardExternalCupCochain; the item's import closure
still needs it, so this is import minimization, not a globally pruned module.
