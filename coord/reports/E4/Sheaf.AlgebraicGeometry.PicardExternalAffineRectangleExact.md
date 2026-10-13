## What changed

Replaced the earlier sandbox's equivalent Exact/Mono/Epi repackaging with a genuine
reduction along the node's affine comparison route. The original module's declaration
signatures, public imports, definitions and zero-map instance are unchanged.

`PicardExternalRectangleSections` constructs the canonical map on every rectangle from
the actual two pullback adjunction units, their restrictions, and tensor sections.
Its coefficient naturality is proved by tensor extensionality, adjunction-unit
naturality, compatibility of module morphisms with restriction, and
`whiskerRight_app_tmulSection`. The map does not require affine opens or quasi-coherence
for its construction or naturality. Only its bijectivity on affine rectangles is
split off as a named theorem.

`PicardExternalAffineRectangleComparison` proves the short-complex comparison from
these canonical maps: it converts their bijectivity into term isomorphisms and uses
`ShortComplex.isoMk` with the two proved naturality identities.

The original theorem now applies `picardScalar_affine_sections_exact`, tensors the
resulting short exact sequence over the field with the scalar sections of G using
`ShortExact.map_of_exact`, and transports it through the proved comparison using
`ShortComplex.shortExact_of_iso`. The new imports in the original module are
proof-only. All three modules compile together in dependency order with `lcompile.py --all`,
with no compiler warnings. The route is the affine local argument in
[Stacks Tag 0BED](https://stacks.math.columbia.edu/tag/0BED), read online because the
literature text is absent on this machine; no global compactness or diagonal
hypothesis is needed on one affine rectangle.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.Modules.picardExternal_affine_rectangle_exact`
(node `lem-sc-picard-external-affine-rectangle-exact`).

Proved the new declarations
`AlgebraicGeometry.Scheme.Modules.picardExternalRectangleSectionsMap_naturality`
and `AlgebraicGeometry.Scheme.Modules.picardExternal_affine_rectangle_comparison`,
as well as the comparison module's zero-map instance. The new definitions are
explicit constructions and contain no holes.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalRectangleSectionsMap_bijective`
(node `lem-sc-picard-external-rectangle-sections-bijective`). Its statement concerns
one quasi-coherent coefficient pair and a fixed explicitly constructed map; it
assumes neither a short complex nor exactness. Its docstring and node give the
affine fibre-product, pullback-sections, tensor-sections and balancing argument,
including empty opens and zero coefficients. The proof of the target combines
this strictly geometric step with the existing affine section exactness theorem
and Mathlib's flat-tensor exactness. This is a decomposition: one hole closed and
one added, not a net reduction in the number of holes.

## No longer needed

Removed the earlier unpublished sandbox module
`Sheaf.AlgebraicGeometry.PicardExternalAffineRectangleExactParts`, its import,
`picardExternal_affine_rectangle_components`, and node
`lem-sc-picard-external-affine-rectangle-exact-parts`. They merely repackaged the
whole conclusion. Removed the stale probe source and the previous purported
second-reading report. None of these was part of the repository baseline.

No existing baseline import is removed. In the new comparison module the second
reader removed the redundant public import
`Sheaf.AlgebraicGeometry.TensorPullback` (already available through the public
scalar-section module) and the unused proof import
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`. Neither removes a module from
the targets' overall import closure.

The old direct dependencies
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-module-pullback-quasi-coherent`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections` are no longer used
by the exactness theorem directly: they remain the geometry plan of the new
bijectivity node. No old dependency is globally pruned. The original node's proof dependencies now follow the actual
Lean assembly; the two new nodes account for the comparison and geometry.
No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous ABANDON treated the absence of an assembled natural short-complex
comparison as an obstruction. It is not: the explicit maps are constructed and
coefficient naturality follows from the existing unit and tensor-section APIs.
The previous sandbox's Exact/Mono/Epi conjunction was equivalent to ShortExact,
so its claim of a strictly simpler intermediate theorem and its second-reading
pass were not justified. Both have been replaced, and no previous review is
claimed for the new delivery.

The existing affine pullback and tensor-section signatures provide much of the
remaining geometry, but assembling the canonical rectangle bijection still needs
the two affine restrictions, the product ring computation, and balancing over
that ring. The already proved `externalGlobalSectionsTensor_bijective_of_isAffine`
is for whole affine schemes rather than this arbitrary rectangle; it is a useful
reference for that algebraic computation. The remaining statement is precisely
this canonical bijectivity, with all coefficient naturality already proved here.

## New nodes

`lem-sc-picard-external-rectangle-sections-bijective` is in
`Sheaf.AlgebraicGeometry.PicardExternalRectangleSections`. Its one remaining hole
is the affine bijectivity of an explicit map. Its construction and naturality
are proved, and the source is the affine computation in Stacks Tag 0BED.

`lem-sc-picard-external-affine-rectangle-comparison` is in
`Sheaf.AlgebraicGeometry.PicardExternalAffineRectangleComparison`. It is proved
from the former node by assembling the three canonical term isomorphisms and
using the proved naturality for the two arrows. It has no ShortExact hypothesis.
Searches for both nodes covered LeanSearch (service unavailable), LeanFinder,
Loogle, Mathlib, the source library, and the existing Sheaf rectangle/global-section
modules. No existing declaration directly assembles the needed rectangle map and
its coefficient comparison. No interface change or forced adaptation is made,
so no change record is required.


## Second reading by E4

1. **Interface: pass.** Compared the original module with the repository by
   `diff -u`. Its two existing declarations and named instance retain their
   signatures byte for byte; its coefficient-functor definition, instance proof,
   docstrings and public imports are unchanged. Only two proof imports and the
   theorem proof are added. The existing node changes only `proof`, `proof_deps`
   and `proof_origin`. Both other modules and their nodes are new. No change
   record or forced adaptation is required.

2. **Proof and data: pass, conditional on the named open geometry theorem.**
   Compiled all three modules in dependency order using `lcompile.py`; no errors
   or warnings. There is exactly one delivered `sorry`, in
   `picardExternalRectangleSectionsMap_bijective`, with its docstring and node.
   No prohibited declaration or hollow definition occurs. The maps use explicit
   adjunction-unit section pullbacks, restrictions, and `TensorProduct.lift`.
   The chosen upstream adjunction is pinned by its unit's formula on every
   section, which determines the unit used here; this is not arbitrary data
   chosen from mere existence. Inverses in the comparison are determined by
   bijectivity. The separate axiom scratch probe and delivery probe check the
   definitions, naturality, comparison and exactness for only the permitted
   axioms and inherited `sorryAx`.

3. **Split statements: pass.** Matched the bijectivity node with its Lean:
   one field, arbitrary schemes and structure maps, two affine opens, two
   quasi-coherent modules, and bijectivity of the fixed canonical map. There is
   no short complex or exactness assumption. This is strictly the geometric
   comparison step, not a restatement of coefficient exactness. For both
   factors Spec(k) the map is the ordinary tensor map; for empty opens or zero
   coefficients both sides vanish. For general affine coordinate rings the
   balanced base-change identity in the docstring proves the claim. Read
   Stacks Tag 0BED's affine case and coefficient diagram online. Independent
   LeanFinder, Loogle and Mathlib grep searches, and `rg` in Sheaf and upstream
   module-section sources, found no duplicate rectangle theorem. Read the
   existing global affine bijection: extending it here requires the open-
   restriction and pullback comparisons, so it does not close this hole in a
   few minutes. The other new theorem assumes only a short complex and derives
   its isomorphism from term bijectivity and proved coefficient naturality.

4. **Route and pruning: pass.** The target proof first uses the existing
   affine scalar-section exactness, then Mathlib flat tensor exactness over k,
   then transports across the natural comparison. Naturality is proved on pure
   tensors from unit naturality, restriction naturality and tensor-section
   naturality. Both short-complex arrow equations have the correct direction.
   Removed the two redundant imports listed above; removing Dual breaks the
   zero-map instance, and removing Closed.Braided from the exactness module
   breaks finite-colimit preservation, so those needed imports are retained.
   Listed all four old geometric dependencies moved below the new bijectivity
   node. Read `dag/units/sk-prop-av-cube.json`: its `realized` entries are already
   empty in the baseline, and the blueprint text is absent on this machine.
   This delivery changes neither that record nor its general-cube/face
   cancellation route; it only assembles a lower affine Kunneth step.

5. **Nodes: pass.** Opened all three delivered JSON records and each referenced
   dependency's Lean/mathlib record. The existing node's three steps match
   scalar exactness, tensor exactness and transport; the comparison node matches
   its three isomorphisms and two naturality equations; the bijectivity node
   separates the proved construction/naturality from its open affine geometry.
   New nodes have source, searches, creation, ancestry, chapter, unit and
   verbatim Lean statement records. No definition or target statement changes.

Second reading changed only two imports in the new comparison module and the
report's explicit dependency/pruning inventory. One original hole is closed and
one simpler hole is added: this is a decomposition, with no claimed net proof
progress or global module pruning.
