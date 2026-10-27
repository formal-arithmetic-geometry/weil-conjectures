## What changed

The statement and public imports of
`Sheaf.AlgebraicGeometry.SymmetricProjAffineComparisonExistence` are unchanged.
Its proof now constructs the quotient as the adjoint of a normalized section map,
proves invertibility of its target, and constructs every affine comparison by
composing chart isomorphisms with the tensor-pullback composition comparison.
The compatibility equation is cancellation of an isomorphism with its inverse.

The invertibility argument is included, not assumed: symmetric-algebra induction
shows that degree-one standard opens cover each affine Proj; the existing twist
invertibility theorem then applies. Invertibility descends across the affine
relative-Proj chart cover using the existing rank-one local-freeness API.

Two new proof imports state the remaining distinct source steps:
`SymmetricProjGluedSections` and `SymmetricProjNormalizedQuotientEpi`.
Private imports of `Modules.LocallyFreeRank`, `Modules.ProjectionFormula`, and
`RelativeProj.Functoriality` provide local-freeness descent, the comparison between
the two invertibility notions, and the relative-Proj chart-cover theorem.
The item's node records this route. No existing shared interface is changed.

Validation through `lcompile.py`: the complete item compiles cleanly in 15.9 s.
The two new modules compiled in 23.3 s and 30.0 s, respectively.

## Proved and sorry left

This is a decomposition, not a net proof of the full construction. One original
hole is replaced by two strictly smaller source obligations.

Closed in the item:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_affine_comparison_with_chart_compatibility`.
Its proof is complete from the two named intermediate statements. The private
helpers `comparison_iso`, `affineComparison_of_quotient`, `symmetric_degree_one_cover`, and
`invertible_of_symmetric_twist_charts` have complete proofs.

Added holes, one per new module:

- `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_symmetric_twist_sections`
  (`lem-trf-symmetric-proj-glued-sections`): gluing the affine degree-one modules
  and normalized map. It asserts neither invertibility nor epimorphy, and does
  not assert existence of a TautologicalQuotient or affine comparisons.
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.epi_of_symmetric_twist_sections`
  (`lem-trf-symmetric-proj-normalized-quotient-epi`): for arbitrary supplied module,
  charts and normalized map, its adjoint is epic. This is solely a local generator
  calculation and asserts no existence or gluing.

There are zero remaining holes in the item and two in the delivered new modules.
Neither a definition nor a private declaration contains a hole.
The new statements allow an empty base, the zero module, and infinitely generated
quasi-coherent modules. In these cases degree-one standard opens still give the
required cover; zero or nilpotent generators contribute empty standard opens.
No finite rank, finite type, or nonemptiness hypothesis was introduced.

## No longer needed

No existing import, module, or node is withdrawn. All three original definitional
dependencies remain needed. No existing dependency is claimed pruned.
The separate construction of the affine restriction comparison by homogeneous
fractions is unnecessary after the global charts exist: categorical composition
constructs it and proves its equation. Fraction descent remains needed only for
gluing the twists, in the first new obligation.

## Where the brief, the DAG or earlier work was wrong

The original node listed definitions and relative-Proj existence but did not
provide the construction of a glued normalized degree-one module or its quotient
map. Its single fraction-comparison step concealed these two distinct tasks.
The existing downstream normalized-descent and quotient-geometry results cannot
supply them here because their proofs depend on this item. The new route exposes
these tasks while proving the remaining invertibility and comparison arguments.
No statement is disputed and no target or existing definition is changed.

## New nodes

`lem-trf-symmetric-proj-glued-sections` records the gluing and normalized section
map of Stacks Constructions Tags 01NR and 01OB, specialized to the fixed canonical
symmetric graded algebra. Its docstring gives the fraction maps, cocycle argument,
and section normalization. Its new Lean module is `SymmetricProjGluedSections`.

`lem-trf-symmetric-proj-normalized-quotient-epi` records the local-generator
surjectivity step of Tags 01OB and 01O4. Its docstring explains the degree-one
standard-open cover, the frame, the lift of scalar multiples, and local epimorphy.
Its new Lean module is `SymmetricProjNormalizedQuotientEpi`.
There are no change records because no other existing module or statement changes.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
