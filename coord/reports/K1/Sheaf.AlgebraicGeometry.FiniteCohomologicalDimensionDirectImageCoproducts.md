## What changed

Proved `AlgebraicGeometry.Etale.rightDerivedLowerStar_preservesCoproducts_of_finite_dimension`
with its exact original signature, including arbitrary indexing universe `w`, empty families,
the zero ring, and unbounded complexes. No statement or definition changed.

The qcqs filtered-colimit theorem is already stated directly for module coefficients.
Its natural single-sheaf comparison and the finite-partial-sum lemma give coproduct
preservation for every classical higher direct image. Apply the proved source-library
finite-dimensional unbounded derived criterion with the given bound `c` and `hc`.
Then use the existing proved private `CategoryTheory.preservesCoproducts_of_small` through
`import all`, extending from coefficient-sized indices to all existing coproducts.
No existing theorem was restated in Lean and no auxiliary proof was copied.

Added proof imports:
- `Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts`
- `WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset`

Public imports now explicitly supply `Functor.rightDerived` and the atomic
commutative-module Grothendieck instance needed to elaborate the original public
statement. The old statement/definition dependencies are replaced with their direct
source imports. `tools/import_prune_check.py` passes with no findings. Single-file
remote compilation passes with no warnings (11.2 seconds after pruning).

Read the current blueprint statement and proof under
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/`, Stacks
`etale-cohomology.tex`, `lemma-finite-cd-mod-n-direct-sums`, and all original dependency
signatures. The current unit record has no realized steps; the same acyclic-term route
is retained through the source-library criterion. New DAG attachments record existing
proved lemmas used by this proof, rather than new Lean declarations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.rightDerivedLowerStar_preservesCoproducts_of_finite_dimension`
(node `lem-exc-direct-image-coproducts`). Added 0 holes; split off 0 holes. No `sorry`
remains in the delivered Lean module. The delivery uses the library's existing
filtered-colimit theorem and its dependencies in accordance with the stage-3 brief;
this is not a claim that all transitive dependencies are now sorry-free.

The two new nodes attach already-proved library declarations and add no module or hole.
The arbitrary-universe step was checked against an existing colimit cofan, so it does
not assert nonexistent oversized coproducts. The source support argument needs only
preservation of zero morphisms, supplied by the additive total derived functor.

## No longer needed

Removed direct imports:
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`

Original proof dependencies no longer directly used by this item:
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-module-abelian-derived-direct-image-comparison`
- `lem-sp-grothendieck-enough-injectives`
- `lem-sp-derived-well-defined`
- `lem-pur-kinjective-degreewise-existence`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-weil-pbc-derived-functor-injective-vanishing`
- `lem-kun-finite-cd-acyclic-complex`

The Grothendieck, enough-injectives, finite-dimensional acyclic-complex, injective
vanishing and derived-coproduct mathematics remains inside the already-proved source
criterion. Their standalone Sheaf modules are unnecessary direct imports here.
In particular `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit` and its open
hole are no longer imported by this module. This does not assert that any of these
modules is globally unreachable; other parents can still use them.

Pruned obsolete `tool_uses` entries corresponding to the removed direct proof
requirements. The existing single-sheaf comparison node is used directly. No extra
tool approval entries were added.

## Where the brief, the DAG or earlier work was wrong

The original route unnecessarily passed from module coefficients through abelian
coefficients and torsion before using a theorem already generalized to module
coefficients. Also, the complete abstract unbounded finite-dimensional coproduct
argument already exists in the source library. Reuse makes a new Godement resolution
or spectral sequence unnecessary. Finite A is not needed by this route, but remains
an unchanged hypothesis of the item.

The original plan did not explicitly explain its arbitrary-index-universe claim.
Coefficient-sized colimit existence alone would not justify it. The existing proved
small-support argument handles every existing coproduct without adding a hypothesis.

An initial compile exposed an inferred-universe mismatch in application of that
helper; its universe arguments are now explicit. No tool was changed or bypassed.

## New nodes

`lem-exc-finite-cd-derived-coproduct-criterion` attaches the existing proved
`CategoryTheory.Functor.preservesColimitsOfShape_rightDerivedFunctor_of_rightDerived`
in `WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension`.
It records the abstract acyclic-term combination, not the geometric statement of this item.

`lem-exc-coproduct-preservation-universe-extension` attaches the existing proved private
`CategoryTheory.preservesCoproducts_of_small` in
`Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts`, available via `import all`.
It records a general fact about preadditive categories and existing coproducts;
its proof and small-support helper are already complete. No new Lean statement or
module is introduced. Three kinds of searches and the whole-blueprint search were
performed for both attachments; Mathlib had no exact match.

Change record: `coord/changes/K1-finite-cd-direct-image-proof-imports.md` records the
public-import pruning, unchanged signature, all transitive consumers, and successful
static import-pruning check. No consumer adaptation is needed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
