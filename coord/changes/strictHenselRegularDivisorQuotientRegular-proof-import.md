# StrictHenselRegularDivisorQuotientRegular proof import

## Reason

`Sheaf.Paper.StrictHenselizationLocalStructure` is used only in the domain proof, not in
any public signature or definition. It must be a plain import in the new domain-component module. This record documents the
visibility correction; no existing statement or definition is altered.

## Old

```lean
public import Sheaf.Paper.StrictHenselizationLocalStructure
```

## New

```lean
-- In StrictHenselRegularDivisorQuotientDomainPart:
import Sheaf.Paper.StrictHenselizationLocalStructure
```

The parent imports this component privately for its proof.

## Users

The direct importer imports this module only for the unchanged conjunction theorem.
A source scan over its 142 transitive downstream modules found only the second row
mentioning `strictHenselizationLocalStructure`; that module already imports the local-structure
module itself. Thus the visibility correction requires no adaptation and changes no
statement meaning, including the targets. There are no changed public definitions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Only uses the unchanged conjunction theorem; its signatures and proof need no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Already directly imports StrictHenselizationLocalStructure; no adaptation or statement change. |

## Status

landed 20261013T160714-L-1372756 2026-10-13 (merge of deliver/V3/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular)
