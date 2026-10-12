## What changed

Preserved the signature and public imports of
`Sheaf.AlgebraicGeometry.Cohomology.CechComparisonInverseImage`.
Replaced the sorry of `AlgebraicGeometry.Scheme.Modules.exists_cechComparison_inverseImage`
with Lean existential introduction and application of two new theorem modules, imported privately:

- `Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence`: existence of a normalized
  system on one scheme cover, without any morphism, coefficients, scalar base or naturality square.
- `Sheaf.AlgebraicGeometry.Cohomology.CechComparisonInverseImageCompatibility`: the inverse-image
  square for prescribed normalized systems, without asserting their existence.

Updated the target node's proof, proof dependencies and proof origin to match that composition.
The source is Stacks Tags 01EQ and 01FD. The new docstrings contain the resolution construction,
the boundary compatibility argument, and the augmented pentagon calculation. For arbitrary
prescribed systems the compatibility proof includes relative Cech effacement and uniqueness:
F embeds into the product of direct images of its restrictions to the covering members;
on a tuple intersection, projection onto its first member splits this embedding, and insertion
of the distinguished member contracts each factor's positive Cech complex.

## Proved and sorry left

Closed the original hole of
`AlgebraicGeometry.Scheme.Modules.exists_cechComparison_inverseImage`
(node `lem-pc-cech-comparison-inverse-image`) by a compiling decomposition. No sorry remains
in the item's module. This is a decomposition, not a proof free of sorry dependencies.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.Modules.exists_cechComparisonSystem`, node
  `lem-pc-cech-comparison-system-existence`.
- `AlgebraicGeometry.Scheme.Modules.cechComparison_inverseImage_compatibility`, node
  `lem-pc-cech-comparison-inverse-image-compatibility`.

Thus one upper hole is closed and two lower holes are added (net -1). Both new declarations
have a proof exactly `by sorry`; their source, full proof in words and matching node are supplied.
No data definition was added or changed, and no data was selected in a definition from an
unproved existence statement. All four sandbox modules compile without warnings; the fourth
is an unchanged copy of the existing system interface, used solely to compile against its current
source and omitted from the actual diff by the delivery tool.

## No longer needed

No import was removed. No module or node can presently be pruned from the targets' closure.
The direct proof dependency on `lem-sc-injective-cech-augmentation-quasi-iso` moved under the
new existence and compatibility statements and remains needed there. The system and Ext-map
interface nodes remain statement dependencies. The module-valued, one-scheme comparison
`Sheaf.Paper.CechComparisonMapNaturality` was searched but never imported: it does not state
this abelian Ext comparison between schemes.

## Where the brief, the DAG or earlier work was wrong

The planned injective augmentation theorem addresses one injective sheaf and one row;
it supplies no normalized natural transformation, connecting law, or inverse-image diagram.
The remaining construction and diagram argument therefore need intermediate interfaces.
The compatibility interface is stronger than the original existential square because it applies
to prescribed systems; the relative-effacement uniqueness argument explains this strengthening.

Checked degree zero, empty covers, infinite covers and arbitrary non-quasi-coherent coefficients:
the zero law is gluing; an empty cover forces the scheme empty; total diagonals are finite;
and the argument takes injective resolutions of underlying abelian sheaves. No affine or
quasi-coherence hypothesis was added. The unit's realized statement/steps are untouched;
this node lies below the unit's prescribed route.

## New nodes

`lem-pc-cech-comparison-system-existence` records the independent existence construction.
It is stated in `lean/Sheaf/AlgebraicGeometry/Cohomology/CechComparisonSystemExistence.lean`.

`lem-pc-cech-comparison-inverse-image-compatibility` records the equality for prescribed systems.
It is stated in
`lean/Sheaf/AlgebraicGeometry/Cohomology/CechComparisonInverseImageCompatibility.lean`.

Both inherit the item's chapter and unit, carry verbatim Lean signatures, actual search records,
and the blueprint ancestor and route. No change record is needed: existing signatures,
definitions, visibility and public imports are unchanged. No forced adaptation was made.

## Second reading by B3

1. Compared the delivered target module with the repository version. The existing declaration
   signature and public import are unchanged byte for byte; only private proof imports and the
   proof body were added. Verdict: pass.
2. Compiled all four sandbox modules with `lcompile.py`. There are no compiler errors or warnings,
   no forbidden declarations, and the only remaining `sorry`s are the two named split-off
   theorems. Their docstrings give complete source-based proofs, and both have matching DAG nodes.
   Verdict: pass.
3. Checked the two split-off statements against their signatures and edge cases (degree zero,
   empty covers, infinite covers, and arbitrary module sheaves), and searched the local library
   and Mathlib for existing declarations. They are true, strictly intermediate, and not duplicate
   an existing theorem. Verdict: pass.
4. Traced imports and DAG proof dependencies. The two private imports are used by the target proof;
   no old import or node can be removed, and the unit's realized statement and route remain intact.
   Verdict: pass.
5. Reconciled each node's Lean record, proof steps, dependencies, source, and origin with the
   delivered declarations. The compatibility node records the stronger prescribed-system result,
   while the target remains unchanged. Verdict: pass.

Changed nothing during second reading beyond this report section.
