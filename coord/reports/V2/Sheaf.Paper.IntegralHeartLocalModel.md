## What changed

Replaced the remaining proof hole of AlgebraicGeometry.ProEtale.integralHeartLocalModel
with a complete assembly from two narrower coefficient comparison statements. On the same
strata and charts, finite projective scalar terms are torsion-free and hence free over the
DVR; Noetherian cycles and their homology quotients are finite. Exact inverse image and the
existing proved scalar-realization exactness theorem give the required cohomology comparison.
The existing integralConstantModelHeart theorem gives constructibility in degree zero and
both truncations after explicit normalization of the coefficient monoid instances.

Moved all original scalar-realization declarations, instances, definitions and proof bodies
unchanged into IntegralHeartLocalModelData, publicly reexported by the original module.
IntegralHeartRealizationExact now imports that data module to avoid an import cycle; its
proof and public signature are unchanged. Change record:
coord/changes/V2-integral-heart-local-model-data.md. Its consumer table covers the full
downstream list, and a whole-library textual audit identified the four actual data consumers.

## Proved and sorry left

Original holes: 1, AlgebraicGeometry.ProEtale.integralHeartLocalModel. Its body is now a
complete proof from named declarations, with zero local sorry. This is a decomposition,
not a net proof: one upper hole is closed and two strictly narrower holes are added.
The unchanged relocated data and the existing exactness theorem have zero holes.

New holes, exactly one per new statement module:

- AlgebraicGeometry.ProEtale.integralHeart_projective_local_models
  (lem-sfb-integral-heart-projective-local-models): transports the existing adic
  finite-projective local models to the canonical internal realization, with no
  freeness, cohomology comparison, completeness of cohomology or truncation conclusion.
- AlgebraicGeometry.ProEtale.integralHeart_constructible_module_complete
  (lem-sfb-integral-heart-constructible-module-complete): only the Roos completeness
  of one constructible module in degree zero on a Noetherian scheme.

Each statement has its source and a complete natural-language proof in its docstring and
its node. Neither is the original conjunction under another name. The parent performs the
projective-to-free argument, finite-cohomology argument and chartwise homology comparison.

## No longer needed

Removed proof imports from the parent: Sheaf.Paper.AdicStratifiedPerfect,
Sheaf.Paper.CompletedConstantSheafReduction, Sheaf.Paper.ConstantModuleSectionProperties,
Sheaf.Paper.CartesianCoefficients, Sheaf.CategoryTheory.TruncationsAndHomotopyColimits,
Sheaf.Paper.IntegralCohomologicalAdicCriterion, Sheaf.Paper.IntegralModels and
Sheaf.SixFunctors.ProEtale.DerivedCompletion. The first, second, third, fourth, sixth and
seventh remain mathematical dependencies of the split comparisons or existing exactness
proof; this delivery does not claim their withdrawal from the target closure. The small
completion public import already provides the last import's declarations.

The parent no longer needs lem-sfb-dvr-projective-complex-matrix-model: its scalar
complex already has scalar-linear differentials, and Mathlib's finite torsion-free PID
instance proves its existing terms free without replacing the complex or choosing matrices.
The old def-kun-truncations dependency is replaced by the existing proved
integralConstantModelHeart theorem. No module is withdrawn, and no adopted source-library
declaration is removed. The original direct imports of the other adic facts are replaced
by the precise dependencies of the two comparison nodes, rather than counted as pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG describes a short mathematical assembly, but the existing adic declarations use
ring-sheaf modules and localized sites, whereas the item uses internal module objects,
scheme cover families and a separate canonical small scalar realization. They cannot be
applied by simple specialization. The two split statements isolate these transports.
The cohomology and truncation parts of the plan already have a proved categorical
implementation in integralConstantModelHeart, independent of the present theorem.

IntegralHeartRealizationExact depended on the parent module for data only, and its DAG
edges pointed at the parent theorem node. The unchanged-data relocation and corresponding
node dependencies remove that artificial cycle. No mathematical statement is disputed.

## New nodes

- def-sfb-integral-heart-local-model-data: the existing real scalar construction and
  finite-free-model predicate, unchanged and publicly reexported.
- lem-sfb-integral-heart-projective-local-models: the adic-to-internal realization
  comparison for bounded finite projective models (clause (1), before choosing bases).
- lem-sfb-integral-heart-constructible-module-complete: degree-zero canonical Roos
  completeness for one constructible module (clause (2), Completeness).

New statements were checked on the zero complex, a single finite free module, a torsion
module R/pi, the complex [R --pi--> R], negative degrees and the empty scheme. Neither
requires uniform bounds on an infinite family of charts. The projective input allows
rank zero and the completeness assertion allows torsion. Searches of Mathlib and the
whole blueprint found the related adic statements but no theorem for these exact internal
coefficient interfaces. The source is the current blueprint proof and its cited Stacks
and Bhatt--Scholze results. No unit route or target statement changes.

## Statement corrected

The exactness node now cites the relocated data node rather than the local-model theorem. This is a definition-location cross-reference correction only; all Lean signatures and mathematical statements are unchanged. Its base citers are recorded in `statement_change` and remain valid.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
