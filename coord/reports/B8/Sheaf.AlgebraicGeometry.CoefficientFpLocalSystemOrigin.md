## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.coefficientFpLocalSystem_essImage` by a complete Lean
assembly, preserving its signature, docstring and public import. The proof obtains
an etale family of constant charts, makes the actual comparison counit invertible
on each chart, and applies Mathlib `Sheaf.isIso_of_coversTop`. Its etale antecedent
is the sectionwise comparison direct image of F, and its comparison isomorphism is
`asIso` of that same counit. There is no choice of arbitrary data from an
unproved existence statement.

Two new modules isolate strictly different steps: `CoefficientFpLocalSystemEtaleCover`
provides etale constant charts, and `CoefficientComparisonConstantChartCounit`
handles a single constant chart, with no local-system or finite-presentation
hypothesis. The first states no essential-image conclusion; the second assumes
no covering family or global triviality. Their statements include arbitrary
coefficient universes, empty schemes and charts, and zero modules. Both contain
a source and complete proof in words. The parent DAG proof now records the Lean
assembly. No existing definition or statement changes, and no consumer adaptation
is necessary.

## Proved and sorry left

One original hole is closed by decomposition:
`AlgebraicGeometry.ProEtale.coefficientFpLocalSystem_essImage`
(node `lem-pe-coefficient-fp-local-system-origin`). The assigned module has zero
remaining holes. Two holes are added, exactly these named public theorems:

- `AlgebraicGeometry.ProEtale.coefficientFpLocalSystem_etaleCover`, node
  `lem-pe-coefficient-fp-local-system-etale-cover`.
- `AlgebraicGeometry.ProEtale.coefficientComparison_counit_isIso_of_constant_over`,
  node `lem-pe-coefficient-comparison-constant-chart-counit`.

This is a decomposition, not a sorry-free proof of the underlying mathematics:
one hole closed and two added, net minus one. Every new hole is exactly
`:= by sorry` in its own module, and no definition or private helper contains a
hole. The combination of the steps is fully proved using the generic Mathlib
local isomorphism criterion.

## No longer needed

No existing public import, module, or declaration is withdrawn. The parent no
longer invokes `det-pe-finite-local-systems-twist` as one monolithic proof dependency:
the actual dependencies are its etale-chart step and its local-counit step, in the
independent coefficient universe. The old module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist` is not imported by this
proof. Its mathematics remains represented by the new steps and their dependencies,
so this is not a claim to prune that module globally or delete its declarations.

The source-library boundary is unchanged. Redundant direct imports of
`Mathlib.Algebra.Module.FinitePresentation` and `Mathlib.Algebra.Category.ModuleCat.AB`
were removed from the new modules; their APIs are already publicly available through
`CoefficientConstructibleEtaleModules`. That coefficient interface supplies the
size-correct sheafification instances the new signatures need. The parent adds only
private proof imports, including Mathlib's local isomorphism criterion.

## Where the brief, the DAG or earlier work was wrong

The current source has no rework row or B8 return for this item. The existing
`finiteLocalSystemsTwist` theorem has coefficients `Lambda : Type u` lifted into
`Type (u+1)`, whereas the assigned theorem permits `Type (max v (u+1))`. The
nearby comparison, localization, and uniform-model APIs also fix the module Hom
universe to `u+1`. Merely applying those declarations after AsSmall transport does
not accommodate arbitrary v: the equivalence changes site Hom sizes without
making the coefficient category smaller. The new statements isolate actual
parts of the existing Stacks 099Y argument instead of renaming the origin
statement or asserting it again with repackaged hypotheses.

The unit route is retained: finite local-system comparison handles a single
stratum, using etale constant charts and the canonical comparison counit. The
parent is not proved from its own conclusion or from stratified continuity.
Neither a Noetherian hypothesis nor finiteness of the coefficient set is added.
The first compile exposed the already documented successor-universe
sheafification inference issue when using only `ProEtaleSmallModelComparison`;
the established coefficient interface resolves it. The chart-counit statement
requires no finite presentation, and remains valid even if its chart is empty.

## New nodes

`lem-pe-coefficient-fp-local-system-etale-cover`, in
`Sheaf.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover`, isolates the two
geometric paragraphs of Stacks 099Y: model-type open loci and etale sections of
the local Isom torsor. It concludes only covering constant slice charts.

`lem-pe-coefficient-comparison-constant-chart-counit`, in
`Sheaf.AlgebraicGeometry.CoefficientComparisonConstantChartCounit`, isolates
localization of the canonical comparison counit and its constant-model case.
It concerns a single chart of an otherwise arbitrary module sheaf and supplies
the local input to Mathlib's isomorphism criterion. No change record is required:
all existing signatures and definitions remain unchanged.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
