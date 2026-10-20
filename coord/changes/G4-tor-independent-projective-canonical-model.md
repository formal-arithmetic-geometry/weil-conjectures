# ModuleCat.torIndependent_projectiveComplex_tensor

## Reason

Restore the assigned quarantined module after upstream sync 5f7b33eac. Its obsolete
Sheaf model import now names a withdrawn, empty module, so the public statement
cannot see HasDerivedCategory or the model constructor. Both proof dependencies
already publicly import the canonical upstream model. Use that same model here.

## Old

```lean
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The archived source is
quarantine/Sheaf/Algebra/Homology/TorIndependentProjectiveComplexTensor.lean.
Its theorem is already proved, with zero textual sorries.

## New

```lean
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

Restore the complete archived file with only this import replacement. The written
theorem signature, docstrings, proof and all other imports remain verbatim. The
upstream model is the canonical definition recorded on
`def-pc-base-derived-tensor-cohomology-model`; no new model or definition is added.
No target signature or mathematical meaning changes.

## Users

`tools/downstream.py` with `--allow-missing --uses` reports no live downstream
module or use of this theorem. A search of both lean/ and quarantine/ finds no
other Lean consumer. DAG parents remain valid: the theorem's name and written
signature are unchanged and its model now resolves to the canonical upstream
implementation, as do the termwise and flat comparison dependencies. The existing
node attachment and proof dependencies are preserved. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor | G4 | Restore and use canonical public model import; compiles cleanly. |

## Status

landed 20261020T153005-L-2860487 2026-10-20 (merge of deliver/G4/Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor)
