## What changed

Replaced the body of
`WeilConjectures.FiniteReductionTower.finite_reduction_tower_resolving_model`
with the resolving-class and strict-tower construction in the node's plan.
The existing theorem signature and all definitions of `ResolvingModel` are unchanged.
The proof uses the concrete finite-reduction quasi-isomorphism theorem, exact finite
pullback and scalar restriction, the existing functorial flat-term K-flat resolution,
and `deriveFromFunctorialResolution`. It uses the proved principal Koszul strict
replacement for the actual augmentation and source goodness. It constructs the
reduction isomorphism from the scalar normalization and the actual universal counit,
and constructs chi from the inverse augmented resolution and the actual derived
pullback counit. The computation and naturality equations are proved by composition
and cancellation in the whole strict-tower derived category.

Added `Sheaf.Paper.FiniteReductionAdditiveCompatibility` for step 1 alone, and
`Sheaf.Paper.FiniteReductionScalarNormalization` for the normalized scalar-tower
identification of step 6. The latter reuses the already proved quotient tensor/scalar
level comparisons and their pure-generator API. It builds an explicit strict tower
isomorphism, identifying adjacent transitions by their unique generator equation.
All added proof imports are private;
no target, source-library signature, or public import of an existing module changes.

Validation: both new helpers passed the batch compile. The final main module passed
a standalone `lcompile.py` run in 49.5 seconds with no diagnostics. All three files
satisfy the 60-second per-file limit. A source comparison confirms the original
public definitions, structure, theorem signature and public imports are unchanged.

## Proved and sorry left

The item's original one hole is closed in
`WeilConjectures.FiniteReductionTower.finite_reduction_tower_resolving_model`.
One new hole remains:
`WeilConjectures.FiniteReductionTower.finite_reduction_additive_compatibility`,
node `lem-a1-finite-reduction-additive-compatibility`. It is precisely the additive,
shift and cone compatibility step, with none of the resolving-class existence,
quasi-isomorphism preservation, Koszul comparison, reduction computation or derived
counit assertions of the original theorem. Its docstring contains the full termwise
argument. Thus this is a decomposition (one hole closed, one added), not a net hole
reduction. The main module has zero remaining holes. The scalar normalization helper
`WeilConjectures.FiniteReductionTower.finite_reduction_scalar_normalization` has a
complete proof from the existing normalization API and has zero holes.

## No longer needed

Removed the item's explicit proof imports of:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`;
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`;
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`;
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`;
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.

The new helpers also omit unused copied public imports: the additive helper needs
only the concrete completed-tower interface and Mathlib cone APIs; the scalar helper
needs only the completed-tower, principal Koszul and coefficient tensor interfaces
for its statement.

The exact finite pullback theorem remains used through the concrete operations
interface; its DAG dependency is retained. The levelwise cohomology criterion remains
used. The following former direct proof dependencies and their `tool_uses` entries
are replaced by the concrete proved interfaces:
`lem-pur-change-of-rings-kflat-quasi-iso`,
`lem-sfb-integral-quotient-resolution-normalization`,
`lem-pc-kflat-resolution`, `lem-pur-left-derived-from-kflat-class`,
`lem-pur-kflat-total-tensor-model`,
`lem-weil-pbc-kflat-fixed-tensor-triangulated`, and
`lem-weil-pbc-diagram-kflat-replacements`.
The proof also no longer directly requires `def-weil-pbc-adic-coefficient-datum`,
`def-weil-pbc-completed-pullback`, `def-pc-tensor-complex-sheaves`,
`def-weil-abstract-derived-category`, `def-pc-sheaf-restrict-scalars`,
`def-a1-flat-term-kflat-complex`, or `def-a1-principal-completed-koszul-towers`
as separate proof steps: their constructions and consequences are supplied by the
retained concrete interfaces or the additive sublemma. These mathematical definitions
remain statement dependencies and/or transitive dependencies where appropriate.
No module is withdrawn and no adopted source declaration is removed. No claim is
made that these modules leave the targets' entire transitive closure. The unit route
is unchanged.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is retained. Several generic dependencies already have proved
concrete independent-universe specializations in `IntegralOperationsWellDefined`,
`IntegralCompletedTowerPullbackUniverses`, `RingedKFlatSingleTensorComparison` and
`PrincipalKoszulStrictReplacement`; reproving those generic results is unnecessary
for this item. The quotient-tensor scalar comparison is also already proved and
provides the stronger arbitrary-complex normalization needed here. The smooth-purity
nodes `lem-pur-integral-operations-well-defined` and
`lem-sf-ringed-kflat-single-tensor-comparison` supply these concrete tools; the
unit's own route has no separate concrete independent-universe replacement for them.
No new maintainer `tool_uses` approval is introduced by this packet. No false statement
or definition repair was found. No change record or forced adaptation is needed.

Advisory from the dependency audit: the existing distant closure contains the
`lem-pc-ring-hom-extension-differential` /
`lem-pc-ring-hom-extension-differential-adjacent` statement/proof cycle, and the already
reported dangling `def-weil-pbc-localization-universal-property` reference. These are
unchanged. A traversal of all new dependency edges finds no cycle back to any of
this packet's three nodes.

## New nodes

`lem-a1-finite-reduction-additive-compatibility` isolates step 1 of the original node:
strict homotopies, canonical degreewise shifts, and normalized cone triangles for the
finite-reduction pullback. This is a proper part of the argument and does not assert
any derived existence or Koszul computation. Its one hole is public and named, with
source and full proof in its docstring. Empty schemes and arbitrary unbounded or zero
complexes cause no extra hypotheses: the argument uses only additive module functors.

`lem-a1-finite-reduction-scalar-normalization` records the canonical generator formula
and strict naturality of the total-tensor/scalar-extension tower comparison used to fix
the reduction counit computation. It reuses
`lem-a1-quotient-tensor-scalar-tower-comparison`. The normalization is valid without
flatness; the good-complex hypotheses merely restrict the domain to what the item
needs. Both new nodes retain chapter `sec-deligne-laumon-a1`, unit
`sk-thm-dl-a1-upper`, and point back to the precise step of the original node.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
