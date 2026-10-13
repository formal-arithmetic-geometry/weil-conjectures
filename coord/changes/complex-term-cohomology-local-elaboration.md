# AlgebraicGeometry.Etale.nonempty_isColimit_complex_term_cohomology

## Reason

The static interface checker treats the added local attribute commands as a change
requiring a record. These commands control elaboration of this module's proof only.
They fold the expensive pullback and cohomology constructions while reducing the
mapped-complex wrappers. Every existing signature and visibility is unchanged.
The proof's scoped `backward.dsimp.instances` option normalizes instance arguments
when the evaluated cocone point is compared with the existing cohomology point.

## Old

There were no local reducibility attribute commands in the original module.
The theorem signature is unchanged, verbatim as recorded in
`dag/nodes/sec-curve-estimates/lem-weil-pbc-complex-term-cohomology-colimit.json`.

## New

```lean
attribute [local irreducible] upperStar upperStarComp upperStarId
  Sheaf.H.map cohomologyMap

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  NatTrans.mapHomologicalComplex NatIso.mapHomologicalComplex
```

These attributes expire at the end of the module's namespace. The elaboration
options are scoped to declarations. No global instance, global attribute, public
import, existing declaration signature or definition body changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity | unclaimed | No interface effect; uses the unchanged theorem. No adaptation. |

The static checker reports a generic command change and finds no named affected
users. This table additionally records the only direct importer and theorem user.

## Status

landed 20261013T163538-L-1620886 2026-10-13 (merge of deliver/M4/Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit)
