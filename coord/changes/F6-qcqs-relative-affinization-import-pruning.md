# AlgebraicGeometry.qcqs_relative_affinization_map

## Reason

The theorem uses quasi-coherence of the structure module and never uses the finite-type
notion defined by CoherentFiniteType. Remove that unused public import while completing
its proof. No declaration signature, definition, universe, or target statement changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
```

CoherentFiniteType is removed. AffineMorphismRelativeSpec is a private proof import;
Mathlib's Affine and Quasicoherent modules explicitly supply IsAffineHom and
IsQuasicoherent in the public statement.
All other existing public imports and the theorem signature stay verbatim. Replace the
unused private Mathlib.AlgebraicGeometry.Modules.Tilde import with
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent, which provides the
proved unit-module quasi-coherence instance actually used by the proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap | F6 | Proof completed; unused import removed. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap
--uses AlgebraicGeometry.qcqs_relative_affinization_map` reports zero downstream modules
and only the declaration in its own module as a textual occurrence. A source search
likewise finds no current Lean importers or callers. No consumer adaptation is needed.
The DAG statement dependencies and parent route are preserved; only the unused rank-one
tilde proof dependency is removed. CoherentFiniteType itself is not withdrawn.

## Status

landed 20261023T123520-L-1203639 2026-10-23 (merge of deliver/F6/Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap)
