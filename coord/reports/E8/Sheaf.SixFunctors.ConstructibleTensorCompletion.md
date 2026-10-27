## What changed

Replaced the hole in `WeilConjectures.constructibleTensorCompletion` by an assembly
of the recorded ordinary tensor model, normalized tensor quotient tower, simultaneous
projective charts, and finite open--closed completion locality. The representative
isomorphism is the restriction of the existing K-flat tensor comparison. The chain
map is the canonical Roos augmentation followed by the normalized whole-tower
isomorphism. The existing ambient-operation comparison theorem supplies the descended
comparison, including its augmentation equation, to the completed tensor.

The new chart statement fixes the existing canonical localization instance explicitly
in its representative isomorphisms. The ordinary-tensor wrapper has the exact
category type of the original theorem; no mathematical operation is replaced.

Six proved helper modules, `ConstructibleTensorCompletionPresentation`,
`ConstructibleTensorCompletionChain`, `ConstructibleTensorCompletionCoordinates`,
`ConstructibleTensorCompletionComparison`,
`ConstructibleTensorCompletionConstructible`, and
`ConstructibleTensorCompletionAssembly`, separate the model comparison, actual chain
construction, coordinate calculations, constructible completeness, and global assembly.
The original combined file profiled at more than 100 seconds, chiefly in normalization
and kernel checking. These modules
use explicitly typed irreducible wrappers for the actual functors and the project's
canonical sheafification instances at the fixed coefficient universe. They introduce
no holes or arbitrary choices. The item privately imports them through the assembly
module. All newly introduced proofs respect transparency.

The finite-tree proof uses simultaneous chart refinement with no additional external
partitions. On every nonempty leaf it turns the finite open charts into a pro-etale
cover, applies the local projective calculation, and uses the locality theorem to
recover global completeness. Empty leaves have empty chart families.

The local projective calculation is isolated in the new module
`Sheaf.Paper.ProjectiveTensorChartComplete`. Its recorded proof compares the two
existing ordinary pullback presentations and applies derived tensor pullback and the
bounded-projective
tensor-completeness theorem. Existing public signatures, definitions, and public
imports of the item are retained.

Validation: all eight delivered Lean modules compiled through `lcompile.py` within
its per-file limit, with no compiler warnings. All new node signatures match the
source, proof-dependency lists equal the unions of the proof-step dependencies, and
the changed DAG has no cycle returning to this item. The original public imports,
seven definitions/instances, and theorem signature were checked verbatim.

## Proved and sorry left

Closed the original hole of `WeilConjectures.constructibleTensorCompletion` by
reduction. Its statement is unchanged. The item module has zero remaining holes.

The helper declarations `ConstructibleTensorModel.tensorCompletionModel`,
`ConstructibleTensorModel.tensorRoosUnit_natural`,
`ConstructibleTensorModel.tensorCompletionChain_app`,
`ConstructibleTensorModel.tensorChain_first`,
`ConstructibleTensorModel.tensorChain_second`, and
`ConstructibleTensorModel.tensorCompletionComparison` have complete proofs. The
constructibility helper's private `tensorUnit_onConstructible` and public
`tensorComplete_onConstructible` prove the global chart-and-locality step.

Added one hole: `WeilConjectures.projectiveTensorChartComplete`, node
`lem-fix-projective-tensor-chart-complete`. This is only the local calculation for
arbitrary inputs whose two ordinary restrictions admit specified bounded
finite-projective models. It has no constructibility assumption, no global tree,
no completed-tensor comparison, and no coordinate normalization conclusion.

Thus this delivery is a decomposition: one original hole closed and one strictly
local hole added, net zero holes closed. All private helpers are proved, and all
new definitions are actual constructions with no `sorry` in their bodies.

## No longer needed

Removed the direct ordinary import of `Sheaf.Paper.IntegralDerivedOperationsOnSlices` from the
item. The chain helper uses `import all` of that module for its existing private
Roos naturality theorem. The presentation helper imports the public ambient-operation
API. None of the helpers is a public import of the item.

Removed the following private module imports from the item module:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.Topology.Constructible`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`
- `Mathlib.Algebra.Homology.Single`
- `Mathlib.CategoryTheory.Triangulated.Triangulated`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.ConstructibleFlatCohomologyTorBound`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.ResidueLisseProjectiveModels`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`

These imports supported the old expanded eight-step plan. The assembled proof now
uses the simultaneous chart refinement and completion locality declarations instead
of reproving their internal arguments. The extra private imports of the bounded
projective theorem and the generic tensor-pullback theorem are also unnecessary in
the item: their local assembly is now the new chart lemma.

The former direct dependencies
`lem-fix-constructible-projective-chart-refinement`,
`lem-fix-qcqs-completion-unit-locality`, and
`lem-pur-integral-ambient-operation-models` are still used inside the proved helpers.
The parent now depends directly on the assembly node instead.

`lem-fix-bounded-projective-tensor-complete` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` remain dependencies of the new
local lemma. Other old ingredients may likewise remain below chart refinement or
completion locality. No existing module, declaration, or mathematical dependency is
claimed globally unreachable or withdrawn. All existing public imports are retained.

The parent's `tool_uses` approvals are kept unchanged (reviewer correction: an existing
node is changed only in `proof`, `proof_deps` and `proof_origin`).

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The existing plan identifies restrictions
of the ordinary tensor using two ordinary pullback presentations, but it had no
single Lean declaration assembling their comparison with the bounded-projective
calculation. The new local lemma states precisely that part. The original item
statement and all target statements remain unchanged. The unit's recorded route
is preserved.

## New nodes

`lem-fix-projective-tensor-chart-complete`, module
`Sheaf.Paper.ProjectiveTensorChartComplete`: ordinary pullback of the canonical
ordinary tensor is complete when the two ordinary pullbacks have bounded
finite-free-retract sheaf models. Its docstring and node give the four-step proof,
the source citations, and the empty-scheme and zero-rank edge cases. This is the
local step of the parent's second proof step. No change records are needed because
no existing public statement or definition is changed.

`lem-fix-constructible-tensor-completion-presentation`, module
`Sheaf.Paper.ConstructibleTensorCompletionPresentation`: proved restriction of the
existing K-flat tensor model and transport of the ambient package's normalized
comparison. Its actual functors and unit have fixed native types.

`lem-fix-constructible-tensor-completion-chain`, module
`Sheaf.Paper.ConstructibleTensorCompletionChain`: proved natural chain map and its
normalized component equation, using the actual quotient augmentation and normalized
tower isomorphism. Its public naturality theorem uses the existing private source
naturality proof; the exported definition refers to that public theorem.

`lem-fix-constructible-tensor-completion-coordinates`, module
`Sheaf.Paper.ConstructibleTensorCompletionCoordinates`: both mapping-fiber coordinate
equations, from the chain module and existing quotient and tower normalization laws.
The six proved helper modules split the profiled construction into separate
compilation units; they add zero holes.

`lem-fix-constructible-tensor-completion-assembly`, module
`Sheaf.Paper.ConstructibleTensorCompletionAssembly`: the complete global proof in the
native total-tensor presentation, combining the separate chart-and-locality proof
with the canonical normalized comparison.
It has no holes of its own. The original item transfers this proved result through
its existing aliases. This proved helper is a compilation split, not a new unproved
restatement or an additional decomposition hole.

`lem-fix-constructible-tensor-completion-comparison`, module
`Sheaf.Paper.ConstructibleTensorCompletionComparison`: proved categorical descent and
normalization of the actual chain map. It composes the completion unit with the
recorded isomorphism and proves invertibility conditional on that unit. Splitting
this fully proved step separates its costly kernel check from global assembly.

`lem-fix-constructible-tensor-completion-constructible`, module
`Sheaf.Paper.ConstructibleTensorCompletionConstructible`: proved finite-tree and
projective-chart completeness of ordinary tensor on constructible inputs, together
with invertibility of its canonical completion unit. This proof uses the one new
local chart lemma and existing simultaneous-refinement and locality declarations.
It has no holes of its own and makes no coordinate or completed-tensor claim.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
