## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.picardExternalCup_zero_tensor` to two strictly
smaller comparisons, leaving its signature and existing docstrings unchanged.
The main proof composes the tensor of the two canonical degree-zero/global-section
linear equivalences, the explicit external-section map made invertible by bijectivity,
and the inverse degree-zero comparison on the product. Injectivity of the latter and
the independent cup formula prove the required pure-tensor identity.

Added `Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison`, with real constructions
of `scalarGlobalSectionsEquiv`, `tensorPullbackTopSection`,
`externalGlobalSectionsBilinear`, and `externalGlobalSectionsTensor`. The degree-zero
comparison uses Mathlib `Functor.rightDerivedZeroIsoSelf`, restricted along the
structure scalar map. Projection section maps use the specified tensor-pullback
adjunction units and restriction to the top open. Their bilinearity is proved,
including compatibility of the scalar maps under composition. No unspecified
existence witness supplies data.

Added the two proof-only imports `ExternalGlobalSectionsTensorBijective` and
`ExternalCupZeroGlobalSections`. All four modules compile without warnings using
`lcompile.py --all`. No existing public import or declaration signature changed. The second reader removed
the redundant new public import of `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`;
the field-linear operations import already supplies the needed instances.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.picardExternalCup_zero_tensor`
(node `lem-sc-picard-external-cup-zero-tensor`). This is a decomposition, not a
sorry-free proof of the geometric theorem: one upper hole is closed and two lower
holes are added, so the net hole count is -1.

The delivery leaves exactly these two named holes:

- `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective`, node
  `lem-sc-external-global-sections-tensor-bijective`, in its own new module. This
  asserts bijectivity of the constructed map on ordinary sections; it contains
  no cohomology comparison or external cup assertion.
- `AlgebraicGeometry.Scheme.Modules.externalCup_zero_globalSections`, node
  `lem-sc-external-cup-zero-global-sections`, in its own new module. This computes
  the degree-zero cup under canonical comparisons for arbitrary coefficient
  modules; it asserts no invertibility and requires none of the geometric
  quasi-compactness, affine-diagonal or quasi-coherence assumptions.

All supporting definitions and private lemmas are proved, with no holes in data.
Both residual statements were checked mathematically for empty schemes, zero
coefficients, and zero sections. The first uses two finite sheaf equalizers, not
an asserted isomorphism between tensor total and product-cover Čech complexes.
The second is the evaluation-at-one calculation of the specified Ext operations.

## No longer needed

Removed the redundant new import `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
from `ScalarGlobalSectionsComparison`. No existing import was removed: the three
existing public imports remain needed
for the statement. The direct target proof does not need
`Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine`
(node `lem-sc-cech-comparison-map-iso-affine`) or
`Sheaf.Paper.CechCupPullbackCompat`
(node `lem-sc-picard-cech-cup-pullback-compat`). Degree zero is compared directly
by the proved Mathlib right-derived-zero isomorphism, and cup compatibility is
isolated as the evaluation-at-one statement. These two planned dependencies
are no longer on this node's proof route; this does not claim other users no
longer need them.

The affine-diagonal, affine product, affine pullback-section and affine tensor-section
nodes remain needed for the new ordinary-section bijectivity node:
`lem-sc-picard-affine-diagonal-intersections`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
They are not pruned from the expanded proof DAG, and the field-linear operations
node `def-sc-field-linear-module-cohomology-operations` remains needed for the
canonical constructions and cup comparison. These five old direct proof dependencies
are relocated beneath the new nodes, not removed from the expanded argument. Together
with the two bypassed comparison nodes above, this accounts for all seven old
`proof_deps`. No whole project module is claimed to leave the targets’ import closure.

## Where the brief, the DAG or earlier work was wrong

The old dependencies give chartwise affine identities and general Čech comparison
statements, but do not package the two global equalizers or identify the recorded
Ext-based scalar operations with those canonical degree-zero comparisons. This
delivery makes those missing interfaces explicit instead of importing lemmas
whose conclusion is not the needed equality.

The local repository does not contain the Stacks `.tex` source files named by the
node. Read the authoritative online sources instead:
https://stacks.math.columbia.edu/tag/0BED (lemma-kunneth and
 equation-kunneth-on-cech), https://stacks.math.columbia.edu/tag/01DZ (module
cohomology definition), and https://stacks.math.columbia.edu/tag/0FKV
(lemma-diagrams-commute). Tag 0BED explicitly omits the final degree-zero cup
verification; the new cup node supplies its evaluation-at-one argument in words.
The unit `sk-prop-av-cube` has empty `realized` lists, and this local reduction
changes no unit statement or step. No statement is disputed.

LeanSearch returned Internal Server Error and is recorded unavailable. LeanFinder
and grep found section/tensor definitions and general degree-zero derived-functor
lemmas, but no full geometric bijectivity or scalar external-cup comparison.

## New nodes

`def-sc-scalar-global-sections-comparison` records the canonical degree-zero
comparison, tensor-pullback top-section map, explicit bilinear external sections
map, and its tensor lift. Its module contains real data and proved linearity.

`lem-sc-external-global-sections-tensor-bijective` records the two finite-cover
equalizers proving bijectivity of that explicit ordinary-section tensor map.
The docstring and node retain the affine formulas and their required assumptions.

`lem-sc-external-cup-zero-global-sections` records the evaluation-at-one formula
for arbitrary module sheaves. It contains the omitted degree-zero verification
from Tag 0BED, separated from geometric invertibility. No change records or forced
adaptations were needed.


## Second reading by F3

1. **Unchanged interface — pass.** Diffed every delivered module against the repository.
   Only `PicardExternalCupZeroTensor` existed there; its sole existing declaration’s
   signature and docstring are byte for byte unchanged. Its changes are two private
   imports and the proof body. The other three modules are new. No statement or data
   definition of the existing library was altered; no change record is required.
2. **Kernel proof and real data — pass, with the reported holes.** Compiled all four
   modules in import order with `lcompile.py --all`, without errors or warnings.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, and
   `Quot.sound` for all four new public constructions. The main theorem and the two
   residual theorems additionally use `sorryAx`, as expected. Scanned the delivered
   sources: exactly the two reported named theorem holes, no forbidden declaration,
   and no hole in data or a private helper. The tensor-pullback adjunction existence
   theorem specifies its unit on every section, so the chosen unit used here is
   determined, rather than an arbitrary existence witness. The equivalence in the
   main proof is the inverse of a fixed bijective map, not a chosen unspecified map.
3. **Residual statements — pass.** Read both full signatures and docstring proofs
   against the scalar operations and normalized adjunction definitions. Bijectivity
   is an ordinary-section assertion; the cup formula has no geometric assumptions
   and asserts no bijectivity. Neither alone restates the original conclusion.
   Finite covers give two sheaf equalizers; tensor over a field preserves their
   kernels and finite products. This proves the proposed geometric statement.
   In degree zero, Ext composition and tensor send unit morphisms to the tensor
   of their sections; the specified coefficient adjunction and pure-tensor formula
   identify this with the constructed section map. This proves the proposed cup
   identity. Empty covers give zero global-section spaces; zero coefficients also
   give zero on both sides, and zero input sections give zero by bilinearity.
   Independently searched with LeanFinder (product-scheme sections/pullback
   bilinearity), Loogle (`Abelian.Ext.mk₀, Abelian.Ext.comp`, unavailable identifier
   in that index), and grep (`external.*[Ss]ection|[Ss]ection.*external|mk₀_comp_mk₀`).
   Also searched the repository and read the upstream module Ext comparison and
   the scalar-unit coordinate/unit-cup lemmas. These supply generic degree-zero
   tools or unit-coefficient special cases, not either full residual statement.
   The resolution-to-Ext comparison and finite-cover assembly prevent either
   residual hole from being closed by a short application of those results.
4. **Top-down route and pruning — pass after import repair.** The target proof
   explicitly tensors the canonical comparisons, uses the ordinary-section
   bijection, then proves its pure-tensor formula by injectivity and the cup
   comparison. No positive-degree Kunneth theorem or dependency cycle is used.
   Verified the two bypassed comparison nodes and the five relocated old direct
   dependencies against the original node. Checked `sk-prop-av-cube.realized`:
   its statement and step lists are empty, and this below-unit reduction changes
   neither its statement nor its step. Removed the redundant public Mathlib sheaf
   limits import entirely; compilation confirms it is not needed even privately.
5. **DAG and sources — pass.** Checked node identifiers, chapter/unit, Lean records,
   creation/blueprint provenance, sources, and search records. The main node’s
   two proof steps and dependency union match the composed Lean proof. The new
   residual nodes record the geometric equalizers and degree-zero evaluation
   argument, respectively, with their needed dependencies. Re-read authoritative
   Stacks Tags 0BED, 01DZ and 0FKV online: 0BED gives the Kunneth context and
   explicitly leaves the degree-zero cup verification to the reader. The new
   cup node records that verification as an agent-written argument, not as a
   quoted completed Stacks proof.

Changes by the second reader: removed the redundant public Mathlib sheaf limits
import; made the report account explicitly for all seven old direct dependencies;
added independent residual-lemma search records and this review. No proof or
statement needed repair. One original hole is reduced to two strictly smaller
holes: this remains a decomposition with net holes closed minus added equal to -1.
