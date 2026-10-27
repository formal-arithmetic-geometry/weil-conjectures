## What changed

Filled `affineRealizationRawEvaluation_pullback` by combining two independent
compatibility squares with the existing `rawRestrictedClassNormalization` theorem.
The proof rewrites naturality of its presheaf isomorphism using its prescribed
components and restriction equation, evaluates at the raw class, transports through
the fixed inverse Ext comparison, and applies coefficient-map functoriality.

Added two statement modules. The existing proved
`unit_coherent_raw_evaluation_formula` supplies the raw-evaluation equation.
The returned delivery's conflicting public helper has been deleted, rather than renamed.
Its consumer now imports and uses `RawRestrictedClassNormalization` directly.
Validation: all three repaired modules compiled through `lcompile.py --all`
(exit code 0); the main module compiled in 47.2 seconds, within the 60-second limit.
No profiling options remain.

All original public imports and declaration signatures are unchanged. No definition,
target, upstream source module, or consumer module changed.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.affineRealizationRawEvaluation_pullback`
(node `lem-weil-pbc-affine-raw-evaluation-pullback`). Zero holes remain in the item.

Added two strictly smaller holes, each exactly `:= by sorry`:

- `AlgebraicGeometry.Etale.sheafHDerivedEquiv_symm_restriction`
  (`lem-weil-pbc-sheaf-h-derived-pullback`): inverse fixed evaluation transports normalized
  chart restriction for arbitrary abelian sheaves. No coherent coefficient or raw class occurs.
- `AlgebraicGeometry.Scheme.Modules.coherentEtaleRestrictionIso_composition`
  (`lem-weil-pbc-coherent-etale-restriction-composition`): equality of coefficient
  sheaf maps on the chart triangle. No cohomological degree or raw class occurs.

This is a decomposition: one upper hole closed and two lower holes added, net +1.
It is not a complete proof using only the three permitted axioms. Each remaining
statement has its source, full proof in words, and matching DAG node. Both squares
apply to empty charts, zero sheaves, and identity maps; the evaluation equation also
applies in degree zero and to arbitrary scheme morphisms. No extra hypothesis was added.

## No longer needed

No existing module or import is withdrawn. Pruned: none.
The session-local duplicate raw-evaluation equation was removed in favor of the existing
`Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormulaAux` theorem; no new API for it
is delivered.

Removed the two proof imports `Sheaf.AlgebraicGeometry.RawRestrictedResolutionNaturality`
and `Sheaf.AlgebraicGeometry.RawRestrictedResolutionRestriction` from
`SheafHDerivedPullback`, together with the conflicting helper
`AlgebraicGeometry.Etale.rawRestrictedCohomologyComparison_naturality`.
The main proof now imports `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization`
and reuses its existing presheaf isomorphism and restriction formula. The resolution
nodes remain dependencies of that existing theorem; they are not withdrawn.
The initially added main proof import `Sheaf.AlgebraicGeometry.SheafHDerivedNaturality`
remains needed by the postponed evaluation square's proof, not the current assembly. The initially added
`WeilConjectures.AlgebraicGeometry.DerivedSectionSingleUnit` import is absent because
its use remains in the postponed generic evaluation square; its node stays a proof
dependency. Original single-unit, tensor-coherence and tensor-section obligations
remain needed below the two new statements. The unit and chapter routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned head `d1cad246d` introduced a public name already declared by
`WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality`.
The signatures differ: that existing theorem varies the source scheme and coefficient
sheaf over a fixed base chart; the rejected helper restricted a chart for a fixed
scheme morphism and coefficient sheaf. Neither existing source declaration nor any
consumer is changed. Instead of renaming the helper, this repair removes it and
reuses the existing chart-normalization theorem, which states exactly the required
presheaf naturality and restriction data. The corresponding DAG step and new-node
dependencies have been updated. Comparison with current main shows the assigned
module's original signature and public imports remain identical.

The single-unit declaration alone does not state compatibility with evaluation of
an arbitrary shifted Ext morphism. The section formula of a single coherent restriction
isomorphism alone does not state compatibility with the structural coefficient map.
Those are the two independent squares now isolated. Neither new statement repackages
the assigned conclusion. No false statement or target change was found.

## New nodes

`lem-weil-pbc-sheaf-h-derived-pullback`, in `SheafHDerivedPullback.lean`, isolates the
fixed-evaluation part of original step 2. Source: Stacks 01FT, 03FD and derived
adjunction 07A6. The statement is exactly the normalized chart square needed by the parent;
it is independent of coherent coefficient transport and raw higher-image classes.

`lem-weil-pbc-coherent-etale-restriction-composition`, in
`CoherentEtaleRestrictionComposition.lean`, isolates the underived coefficient square
of original step 3. Source: tensor-section functor 03DR and restriction 03Q8.
No definition or existing interface changed, so no change record is required.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
