# WeilConjectures.finiteScalarTotalTensorIso_representative_component_eq

## Reason

The proof only unfolds the specialized total tensor isomorphism. The complex module is
therefore a proof-only dependency and is imported privately. Two local elaboration options
and a local irreducibility attribute keep this large component statement within the
single-file compile limit; they are scoped to this module and do not alter declarations
seen by importers.

## Old

```lean
public import Sheaf.Paper.FiniteScalarTensorComplex
public import Sheaf.Paper.FiniteScalarTensorResolution
```

## New

```lean
public import Sheaf.Paper.FiniteScalarTensorResolution
import Sheaf.Paper.FiniteScalarTensorComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] finiteScalarFlatRepresentatives
```

## Users

| module | group holding it | effect |
|---|---|---|

No modules import this item directly on the current tree. The resolution module publicly
reexports the complex module, so its public declarations remain available to importers.

## Status

landed 20261027T180530-L-3871527 2026-10-27 (merge of deliver/D9/Sheaf.Paper.FiniteScalarTotalTensorIsoComponentEquality)
