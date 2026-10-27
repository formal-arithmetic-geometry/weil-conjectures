# AlgebraicGeometry.ProEtale.openScalarRestrictedTransposeExpansion

## Reason

Complete the assigned theorem from the existing canonical open-scalar unit identity,
actual open adjunction naturality and the assumed counit equation for r. Generic private
proved helpers keep large derived-category constructions folded during elaboration.
File-local irreducibility and transparency controls affect proof elaboration only.
The proof-only `import all` accesses the existing proved private `openScalarIso_unit`;
it exports no new dependency to users.

## Old

The theorem body was `by sorry`. There were no private proof helpers or additional
file-local irreducibility/transparency controls. Its signature and the definition of
`openScalarRestrictedTranspose` are preserved verbatim in the delivery.

## New

The theorem has a complete proof and all new private helpers are proved. The original
public signatures and definition body are identical. The proof uses the same actual
open counit and named scalar comparison. No target definition changes.

The local proof controls are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] proEtaleRingDerivedOpenAdjunction
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
  reductionDirectImageComparison openScalarIso directImageScalarPullbackIso tensorPullbackIso
```

Ten redundant public imports are removed, replaced by the narrower existing
`Sheaf.SecSmoothPurity.ReductionDirectImageComparison` definition interface. The
complete removed-import list is in report.md. The statement's definitions are
still public; no current downstream Lean module relies on the removed reexports.

## Users

`python3 tools/downstream.py Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion
--uses openScalarRestrictedTranspose openScalarRestrictedTransposeExpansion` reports zero
current Lean importers. Neither public declaration changes signature or meaning.
The item is retained: unfinished DAG parents still require it. No consumer adaptation
or module withdrawal is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | J1 | Proof completed. |

## Status

landed 20261024T190053-L-3905073 2026-10-24 (merge of deliver/J1/Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion)
