# AlgebraicGeometry.Scheme.adicResidueAdjointTower

## Reason

Expose the concrete normalized scalar tower and the existing Cech reflector assembly
so the complete-reduction-cone proof reduces to a comparison of actual constructions.
The existing item statement and public imports stay verbatim.

## Old

No declarations with these new names existed. The item proof was `by sorry`.

## New

New modules `Sheaf.Paper.AdicResidueAdjointTower`,
`Sheaf.Paper.AdicResidueCompletionModel`, and
`Sheaf.Paper.AdicResidueCechQuotientCone` carry the declarations attached to their
matching new DAG nodes. The first constructs the unique scalar adjunction whose unit
is `adicFiniteUnit`, defines each successor by transposing the reduction of its counit,
and proves naturality for every transpose. The second proves finite generation of the
slice kernel and applies the existing Cech completion model. The third states the
remaining unit-preserving comparison, as one named theorem with `by sorry`.

The item proof uses the Cech reflector's invertible unit, the comparison cone and the
proved scalar-transpose equation. Its full signature is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompleteReductionCone | C6 | Proof uses the new constructions; signature unchanged. |
| Sheaf.Paper.AdicResidueCechQuotientCone | C6, new | Statement uses the explicit tower and Cech model imports. |
| Sheaf.Paper.AdicCompleteHomSections | unclaimed | Original imported signature unchanged; no adaptation. |

No existing public signature or definition body changes. No target statement changes,
and no target definition changes its meaning. No forced consumer adaptation is needed.

## Status

landed 20261025T201559-L-2582137 2026-10-25 (merge of deliver/C6/Sheaf.Paper.AdicCompleteReductionCone)
