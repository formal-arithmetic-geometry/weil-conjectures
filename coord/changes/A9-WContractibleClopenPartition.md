# AlgebraicGeometry.Scheme.proetale_wContractible_clopen_partition

## Reason

The completed proof reuses the existing scheme-level split-cover theorem
`AlgebraicGeometry.exists_comp_eq_id_of_isWContractibleRing` and Mathlib's finite
coproduct and weakly etale APIs. The previous sorry proof imported the planned unit
route modules `Sheaf.AlgebraicGeometry.EtaleComparison`,
`Sheaf.AlgebraicGeometry.WeaklyEtaleStability`, and
`Sheaf.RingTheory.WContractibleGeometricCriterion`, plus several Mathlib modules
whose APIs are already available through the retained imports. Those imports are
removed from the item proof. The proof needs `Limits` opened for `Sigma`, coproduct
and open-range declarations; this is now `open CategoryTheory Limits`.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.RingTheory.WContractibleGeometricCriterion

open CategoryTheory
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

open CategoryTheory Limits
```

The theorem statement and all declaration signatures remain identical. The added
`Limits` namespace command is required by the proof and is harmless to users. The
node copy records the corresponding proof route and removes the unused direct proof
dependencies and tool-use approvals.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition
--uses proetale_wContractible_clopen_partition` reports 862 downstream modules and
one textual declaration user, the item itself. Public imports and signatures are
unchanged; all removed imports were plain proof imports. Downstream modules retain
the same public interface and require no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition | A9 | Complete the sole theorem proof; prune plain proof imports and open Limits for its proof. |

The item itself is the only module changed in this delivery. The removed
unit-route modules remain available to their other importers and are not withdrawn.
The node file is updated only to describe the actual proof and its dependencies.

## Status

landed 20261019T002501-L-2140069 2026-10-19 (merge of deliver/A9/Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition)

