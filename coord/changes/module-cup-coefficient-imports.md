# Sheaf.Paper.ModuleCupGodementCoefficientComplexes imports

## Reason

Prune the unused existential Godement-pairing theorem and replace its re-export with the
four explicit statement dependencies it previously supplied. The proof uses compatible
cosimplicial models and natural Alexander--Whitney maps instead. The theorem's existing
signature, universe, binders and visibility remain identical. No definition changes. The proof-only `import all` reuses the existing private
`modelFlasque` helper instead of duplicating its proof.
The local `open` list also includes AlgebraicTopology and Simplicial for the proof helpers.

## Old

```lean
public import Sheaf.Paper.ModuleCupGodementPairing
open AlgebraicGeometry TopologicalSpace
```

## New

```lean
public import Sheaf.Paper.ModuleCupResolutionData
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Paper.ModuleCupGodementCoefficientModels
import Sheaf.Paper.ModuleCupGodementModelQuasiIso
import all Sheaf.Paper.ModuleCupGodementCosimplicialInput
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
```

## Users

The downstream scan with `--uses moduleCup_godement_pairing` found no use of the declaration
whose public re-export is removed. The four required public statement dependencies are explicitly retained.
The unused `Mathlib.Algebra.Homology.Embedding.IsSupported` re-export is removed
as requested in return H9; it is not a required replacement import. The direct and transitive downstream modules reported by the current scan are:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupCoefficientResolutionMaps | unclaimed | No theorem signature changes; no reference to the removed pairing declaration; no adaptation. |

No existing dependent module is delivered or modified. The sole existing theorem's exact
statement is preserved; no target definition or target statement changes.

## Status

landed 20261014T022540-L-4043749 2026-10-14 (merge of deliver/A3/Sheaf.Paper.ModuleCupGodementCoefficientComplexes)
