## What changed

Completed the unchanged theorem
`AlgebraicGeometry.ProEtale.SpTowerProjection.tower_projection_domain_evaluation`
in `Sheaf.Paper.TowerProjectionDomainEvaluation`.
The proof obtains bounded level representatives, proves their signed tensor totals have
support in the sum interval, and transfers these bounds to towers through exact evaluation.
It proves naturality of the actual open inverse comparison by its adjunction mate and uses
the existing recorded proper/open evaluation laws and direct-image naturality.
Private proved helpers isolate the tensor-model comparison and the elementary support and
cohomology arguments. The public definition `levelOpenComplex` is unchanged.
The item's DAG proof is updated to describe the Lean proof.
The complete module compiled without warnings in 48.1 seconds via `lcompile.py`.
No definition, statement, source-library module, or consumer interface is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.SpTowerProjection.tower_projection_domain_evaluation`
(node `lem-sp-tower-projection-domain-evaluation`). No holes added; no sorry remains in
the delivered module. Every private helper has a complete proof.
The imported `maps_natural`, `properMap_evaluation` and `openMap_evaluation` declarations
are existing statements, not new holes or applications of the parent's projection formula.

## No longer needed

Mathlib's `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` supplies the bounded
representative directly, so this proof does not need `def-kun-truncations` or the private
import `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
The private import `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` and its
old direct proof dependency/tool-use entry are also removed.
The one-K-flat tensor comparison is supplied by
`Sheaf.Algebra.Homology.RingedTensorComparisonExtension` for the actual prescribed
level closed structure. No module is withdrawn, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The Tor-amplitude predicate uses `siteDerivedTensorIndependentCoefficients`, whereas
`torAmplitude_iff_exists_bounded_flat_model` uses `wfSiteDerivedTensor`. These are separately
chosen localization models; a comparison must be supplied before applying the latter theorem.
The proof constructs that comparison from existing descent interfaces.
Endpoint intervals, including equal endpoints, use only weak bounds. Vanishing support and
zero objects are handled by exact functors and the coproduct universal property, including
empty schemes and zero module inputs. The unit's route and the target statements are unchanged.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
