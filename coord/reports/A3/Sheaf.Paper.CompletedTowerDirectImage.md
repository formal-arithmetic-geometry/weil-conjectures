## What changed

Changed only `lean/Sheaf/Paper/CompletedTowerDirectImage.lean`, with change record
`coord/changes/A3-completed-tower-unused-comparisons.md` for the pruning.

The additive instances use the sectionwise definitions. Ordinary limit preservation
specializes the module adjunction. The coefficient comparison is proved invertible
from `proEtale_profinite_coefficient_inverse_image`, retaining the prescribed quotient
projections. Applying the exact-adjoint criterion to the levelwise adjunction proves
K-injective preservation. The limit and evaluation criteria use their existing exact
left adjoints. The evaluation isomorphism already constructed in this module supplies
the former existential theorem, which is moved after that construction.

The ordinary restriction comparison specializes the general section-normalized
comparison and inverts it. Its inverse is proved to be identity on sections, and
sectionwise extensionality gives uniqueness. The derived comparison specializes
`proEtaleRingRestrictionDerivedDirectImage_existsUnique`. A proved categorical
inverse-square lemma converts its orientation and universal-unit normalization to
exactly the normalization required here. Both versions of the complex derived unit
are compared explicitly, including their identity homotopy-category factor.
No arbitrary natural isomorphism is substituted for the prescribed comparison.

Four unused older Roos/completion statements and the eight definitions used only by
them are removed. The current blueprint interface and its obligations in
`CompletedDirectImageLimits` are retained; this is pruning of unused declarations,
not proof of those obligations. All retained public signatures and definition bodies
are unchanged. The only added declarations are proved private helpers.

Validation: the complete final module compiles through `lcompile.py` without warnings
or errors (39.4 seconds). Whole-library searches and `tools/downstream.py --uses`
find no external user of any removed declaration. The general ring-change and
profinite inverse-image proof imports pass the import-direction check. No local Lean
or Lake build was run. The delivery dry run performs the independent mechanical
compile and axiom checks.

## Proved and sorry left

Original holes: 15. Closed by proof: 10. Removed as unused: 4, counted separately.
Remaining original holes: 1. Added holes: 0. Split-off statements: 0.
This is a partial proof delivery of a module with several original holes, plus pruning.

The ten proved declarations, all retaining their original signatures, are:

- `AlgebraicGeometry.Scheme.completedModuleDirectImage_additive`
- `AlgebraicGeometry.Scheme.completedTowerModuleDirectImage_additive`
- `AlgebraicGeometry.Scheme.completedTowerDirectImage_evaluation`
- `AlgebraicGeometry.Scheme.completedModuleDirectImage_preservesLimits`
- `AlgebraicGeometry.Scheme.completedDirectImageLimit_naturality`
- `AlgebraicGeometry.Scheme.completedTowerLimit_preservesKInjective`
- `AlgebraicGeometry.Scheme.completedTowerDirectImage_preservesKInjective`
- `AlgebraicGeometry.Scheme.completedRestrictionDirectImageIso_exists`
- `AlgebraicGeometry.Scheme.completedDerivedRestrictionDirectImageIso_exists`
- `AlgebraicGeometry.Scheme.completedEvaluation_preservesKInjective`

The only `sorry` left in the delivery is
`AlgebraicGeometry.Scheme.completedDirectImageProjectionFormula_properties`
(blueprint node `prop-weil-pbc-direct-image-limits`). It remains exactly its original
statement and `:= by sorry` proof, with its existing source and proof docstring.
No new statement moves or repackages this hole. Its first clause remains used by
`FourArrows.finiteProjection_isIso`.

The four removed original holes are:

- `AlgebraicGeometry.Scheme.completedDirectImage_complete`
- `AlgebraicGeometry.Scheme.completedDirectImageRlim_roos`
- `AlgebraicGeometry.Scheme.completedDirectImageProjectionFormula_quotients`
- `AlgebraicGeometry.Scheme.completedDirectImage_completionUnit`

The proved declarations use existing stated dependencies, some of which still have
their own named holes. No new axiom or hole is introduced in this packet.

## No longer needed

Removed proof-only imports:

- `Mathlib.Algebra.Homology.Functor`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.PbcDerivedProductRepresentation`
- `Sheaf.Paper.KoszulReconstruction`
- `Sheaf.Paper.PbcRoosTriangle`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`

The existing public imports are retained. The proofs use the general exact-adjoint,
whiskering, inverse-image and normalized restriction/direct-image APIs directly.
No new total-derived existence proof or chosen K-injective resolution is needed here.

In addition to the four removed holed theorems listed above, removed the following
unused definitions, which have no occurrence outside the assigned module:

- `completedDirectImageRlimIso`
- `completedLimitEvaluation`
- `completedRlimEvaluation`
- `completedRlimProductMap`
- `completedDirectImageProductMap`
- `completedReductionStep`
- `completedRestrictedProjectionFormula`
- `completedQuotientCompletionUnit`

The current `AdicCoefficientDatum.directImageRlim_roos`, `towerProjection_properties`,
`towerProjection_isIso` and `push_complete` in `Sheaf.Paper.CompletedDirectImageLimits`
remain the live blueprint interface. In particular the strict-tower completion-unit
obligation remains; evaluating the finite-level mates would not prove it.
No DAG node or entire module is claimed globally pruned: other interfaces may still
need every one of those nodes, including Koszul reconstruction and perfect projection.
The removed imports are unnecessary for the proofs delivered in this assigned module.

## Where the brief, the DAG or earlier work was wrong

The module's docstrings point to `prop-weil-pbc-direct-image-limits`, but that node's
current `lean` attachment points to `Sheaf.Paper.CompletedDirectImageLimits`, not to
this older module. There is no node whose current `lean.module` is the assigned
module. Accordingly no unrelated node attachment or proof route is overwritten.
The current node and the unit's realization are preserved, including all their
Roos and strict-tower reduction obligations. The pruning change record documents
which unused declarations of the older implementation are retired.

The stated general ring-change comparison is sufficient for ordinary and derived
restriction/direct-image compatibility. Its orientation is opposite to this module's
interface, so inversion and explicit normalization, rather than a new existence
assumption, are required. The previous existential evaluation theorem is supplied by
this module's existing canonical isomorphism and needs no independent construction.

The remaining finite projection-formula property cannot be filled merely by applying
`PerfectProjection.reductionMap_isIso`: that theorem is over the constant finite-quotient
presentation, whereas this module uses the continuous-functions presentation and an
actual scalar-adjunction mate. Comparing the rings alone does not identify the two
specified derived arrows. This packet leaves that statement unchanged instead of
claiming an unproved identification.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
