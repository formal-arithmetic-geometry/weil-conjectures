# coherent_frobenius_comparison

## Reason

Restore the quarantined item with a complete replacement proof of its final
Frobenius pullback step. The quarantine row records an unavailable compiled
CoherentFrobeniusPullback dependency. Its current source also brings together two
resolution-naturality declarations with the same name through separate imports.
The new proof constructs the target etale power map explicitly, proves the
coefficient square using structural section coordinates, and transports the
cohomology square through the proper comparison equivalences. This proves the
proper-case identity required here without that general dependency.

The theorem signature, visibility, public imports, supplied comparison maps,
base-change equivalence, and all target statements stay identical. There are no
changes to existing public definitions or to source-library modules. Private
helpers construct actual data and have complete proofs.

## Old

Archived import block, verbatim:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.CoherentPowerComparison
import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback
import Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.CoherentPowerComparison
import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback
import WeilConjectures.AlgebraicGeometry.EtaleStructureSectionsEquiv
import Mathlib.Algebra.CharP.Lemmas
```

The complete theorem signature is unchanged (verified token for token against
the quarantined source). Only its proof and private supporting declarations change.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison
--allow-missing --uses coherent_frobenius_comparison` reports zero downstream
modules and zero current Lean uses. The unfinished DAG parent
`lemma-weil-pbc-smooth-curve-artin-schreier` still cites the item. Its statement,
Lean attachment and unit route are preserved; the item is restored, not withdrawn.
No consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | Q2 | Restored with unchanged signature and public imports; complete proper-case Frobenius naturality proof. |

## Status

landed 20261020T221311-L-4170598 2026-10-20 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison)
