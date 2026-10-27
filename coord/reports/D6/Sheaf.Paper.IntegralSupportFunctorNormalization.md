## What changed

Reduced the remaining `integralSupportFunctorNormalization` hole to separate open and
closed support comparisons. Its original statement and every field of `Normalization`
are unchanged. The complete assembly constructs the inherited scheme-over structures,
finite-type and quasi-compact instances, transports the base prime unit to residue fields,
obtains constructibility from the actual support functors through dj and di, inverts the
ordinary closed pull map on complete inputs, and restricts the ordinary derived closed
adjunction. Mathlib's fully faithful restriction equations prove all four displayed
ordinary unit/counit formulas; they are not split off as new holes. A proved private
categorical inverse-cancellation lemma keeps these equations abstract and avoids unfolding
the full-subcategory functors during rewriting. Both scalar-linearity
clauses follow directly from the already declared actual support-functor linearity lemmas.

The definitions and the previously proved identity comparison move unchanged to
`IntegralSupportNormalizationData`, publicly re-exported by the old module. A proved
private identity-isomorphism extensionality helper keeps the coefficient ring and functor
abstract and prevents completed-limit unfolding in the existing uniqueness proof.
The two new statement modules import the shared definitions without an import cycle.
No arbitrary data is chosen from the new existence statements by a definition: the main
proof eliminates the two Nonempty statements only to prove a proposition.

Searches used msearch.py LeanFinder, Loogle, LeanSearch and grep, plus project rg.
They found the general full-subcategory adjunction restriction formulas used in assembly,
but no theorem assembling these specified completed-coefficient support comparisons.

## Proved and sorry left

Closed the original textual hole
`WeilConjectures.IntegralSupportNormalization.integralSupportFunctorNormalization`
(node `lem-sf-integral-support-functor-normalization`) by a complete Lean proof from
two strictly smaller obligations. This is a decomposition, not a sorry-free proof:
one original hole is closed and two new holes are added (net minus one).

The two added and remaining holes, each the whole proof of its public theorem, are:

- `WeilConjectures.IntegralSupportNormalization.openSupportNormalization`,
  node `lem-sf-open-support-normalization`;
- `WeilConjectures.IntegralSupportNormalization.closedSupportNormalization`,
  node `lem-sf-closed-support-normalization`.

The item and shared data module contain zero holes. The existing
`identityModuleImage_existsUnique` remains proved. No holes occur in definitions,
private helpers, or the assembly proof.

## No longer needed

Removed the old private proof imports from the item:

- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.SixFunctors.IntegralOpenReductionComparison
- Sheaf.Paper.CompletedDirectImageLimits
- Sheaf.Paper.KoszulReconstruction
- Sheaf.Paper.OpenFiniteConstructibilityInterval
- Sheaf.Paper.ProEtaleConstructibleOrigin
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
- Sheaf.AlgebraicGeometry.ComparisonDirectImage
- WeilConjectures.ConstructibleSheaf.OpenClosed
- Sheaf.CategoryTheory.StrictRoosComparison
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Sheaf.Paper.SfIntegralConstructibleLinear
- Sheaf.CategoryTheory.ExactDerivedAdjunction (retained in the shared data module)

These are not mathematical pruning claims: the old seven-step dependencies are retained
under the corresponding new open and closed obligations. Dependencies confined to the
other support operation are omitted from each individual split; scalar linearity is
proved directly in the item rather than required from either split. No module, node or source-library
declaration is withdrawn. Existing public imports are retained to preserve consumers.
SfIntegralConstructibleTriangulated is retained privately for isomorphism closure.

## Where the brief, the DAG or earlier work was wrong

The seven-step mathematical route remains valid. The existing generic declarations use
several different coefficient/site presentations and system calculi; their signatures
do not directly provide the exact open and closed Normalization fields. The two new
obligations record that missing presentation and normalization assembly separately.
They cannot each imply the original theorem: neither includes the other's operations,
and the closed obligation omits the restricted adjunction and its unit/counit formulas.

Edge cases checked at the statement level: empty open, empty closed, identity open,
zero input, positive exponent one, nonreduced closed subschemes, arbitrary integer
shifts, and empty reduction intervals. No nonemptiness or nonempty interval assumption
was added. All inherited geometry is established in the main proof.

## New nodes

`def-sf-integral-support-normalization-data` owns the relocated original Normalization
structure, closed reduction/limit/alpha maps, evaluation inverse and three existing
shift instances. The two pre-existing definition owners for open identity normalization
and ordinary open operations retain their declarations with updated module attachments.

`lem-sf-open-support-normalization` is only the open support comparison, fixed realization,
finite projection equation, preservation, actual strict-system adjunction equations,
and shift/exact normalization. The ordinary restricted adjunction is pinned to
Mathlib's construction, and its two ordinary component equations are proved in the item.

`lem-sf-closed-support-normalization` is only the closed ordinary comparison, actual
strict-limit comparison, preservation, finite projections, shift/exact clauses,
and empty-fiber composite. Its closed pullback and restricted adjunction are constructed
and their equations proved in the item, not restated as an existence conclusion.

Change record: `coord/changes/D6-integral-support-normalization-data.md`.

Validation: the shared data and both split statement modules compiled through lcompile.py
(result 63e5ad34da87059f7fe871e6). The final item assembly compiled successfully
(result fee2ef76d6da3caa365f9be3, exit code 0). The overlaid import graph has zero cycles;
every delivered node signature matches its declaration and every direct dependency exists.
A textual signature/body comparison confirmed every relocated public signature and every
non-theorem body is unchanged. The complete consumer list is in the change record.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
