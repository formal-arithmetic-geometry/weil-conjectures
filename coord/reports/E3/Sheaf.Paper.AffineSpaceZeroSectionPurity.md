## What changed

Proved AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_baseChange
from the already stated coordinate_section_product_baseChange. Substitute the
structure-map equality and unfold classBaseChange to the same named canonical
source isomorphism as the first clause of the product-recursion identity.
This applies to arbitrary base change, including nonflat maps.

Moved the existing primitive constructions, with all public names and signatures
preserved, into Sheaf.Paper.AffineSpaceZeroSectionConstructions. The item publicly
reexports them. CoordinateSectionProjection and CoordinateTowerNormalizationData
change public import line 3, so the item can use its planned dependency
without an import cycle. The two raw left endpoint proofs simplify their outer
definitions before reflexivity, avoiding full normalization of derived structures.
End the computation section before targetPullbackIso to restore the tensor alias
to its existing implicit reducibility, so its canonical bifunctor can match the explicit
cupMonoidal target. A generic equality check of these presentations passed by rfl.

classBaseChange stays in the item. The item publicly imports CoordinateZeroBaseChange
for its unchanged coordinateSourcePullback. classBaseChange uses its inverse,
exact inverse image and the original target comparison: the same original five
arrows by inverse composition and associativity. A generic Lean expansion check
passed. No declaration in CoordinateZeroBaseChange is changed.

The unclaimed FiniteProductReductionComparisons needed a consumer timing repair.
It prioritizes Mathlib's canonical abelian instance locally and writes the three
canonical isomorphisms defining closedSingleIso directly. This preserves the
component maps and their order, signatures, imports and global attributes.

The shared normalization proof landed during this session. Rebase onto its
CoordinateTowerNormalizationData extraction; preserve that theorem and all its
new proof dependencies unchanged. Only the data module's import is adapted.

The construction and data modules compiled through lcompile.py. Unchanged
current sources along the coordinate-product import chain are also included in
the sandbox solely to compile in full import order: the published normalization
object predates K6's declaration relocation and otherwise duplicates names from
the new construction module. These byte-identical consumers are not code changes
and are omitted from the delivery commit by the delivery tool.
The repaired coefficient comparisons and unchanged FiniteDiagonalOrientationReduction
consumer compiled together. Every original declaration signature in the changed
modules was compared with the shared source and preserved.

## Proved and sorry left

Closed the base-change hole present at the start of this session:
AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_baseChange.
The current shared source also rolled back three proofs present initially.
This packet restores those proofs in the construction module:
AlgebraicGeometry.ProEtale.AffineZeroPurity.targetSourceRaw_left,
AlgebraicGeometry.ProEtale.AffineZeroPurity.normalizationRaw_left, and
AlgebraicGeometry.ProEtale.AffineZeroPurity.unit_finiteTor.
Thus it closes 4 of the current source's 6 holes (1 of the initial 3).
Added 0 holes; split off 0 holes. The proof uses the existing, still holed
coordinate_section_product_baseChange in its stated dependency module.

The item's remaining holes are
AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity and
AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_untwisted,
both attached to cor-pur-affine-space-zero-section-purity. Their original
statements and complete proof docstrings are retained.

The new construction module, CoordinateSectionProjection,
CoordinateTowerNormalizationData and FiniteProductReductionComparisons contain
no holes. No normalization-induction module is included or changed.

## No longer needed

The import of Sheaf.Paper.AffineSpaceZeroSectionPurity is removed from
CoordinateSectionProjection and CoordinateTowerNormalizationData; each now
imports the primitive construction module directly. Their declarations use these
constructions. All original public imports of the item remain.

No mathematical dependency node or module is pruned: the two remaining purity
clauses still have their original proof plans. The base-change proof uses the
product-recursion dependency alone; it does not need the line-adjunction,
twisted-section-normalization, tower-normalization or immersion-twist theorems.
These are retained for the remaining clauses.

## Where the brief, the DAG or earlier work was wrong

The prescribed product-recursion dependency could not be imported by its parent:
its primitive construction imports led back to the item itself. The relocation
repairs that graph while preserving the public names and signatures.

The latest blueprint distinguishes the positive Cartier class c_D from the
localization boundary: partial kappa(t)=-c_D. The current Lean ordinaryBoundary
uses the positive cartier_kummer_map family, so its expected trace-one normalization
agrees with the Cartier clause of the updated blueprint. The old prose's
unconditional identification with the positive localization boundary needs a
later convention review; no sign or theorem statement is changed here.

## New nodes

def-pur-affine-zero-purity-constructions records the existing canonical comparison,
contraction and coordinate pullback primitives in their new module, with
normalization as its primary declaration. No mathematical assertion or proof
hole is introduced. The original node retains the three purity theorems and
classBaseChange. Source: the current zero-section purity proof's composition,
base-change and final comparison paragraphs.

Change record: coord/changes/E3-affine-zero-construction-import-cycle.md.

Change record: coord/changes/E3-closed-source-canonical-abelian.md.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
