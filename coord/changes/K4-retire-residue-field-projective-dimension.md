# Sheaf.RingTheory.ResidueFieldProjectiveDimension

## Reason

Complete the listed retirement in `coord/retire-items.tsv` under the human's
Hand-off in `coord/changes/retire-sheaf-twins-20261020.md`. M1's landed repair
already replaced the old proof copy with a declaration-free public reexport
and attached the mathematical node to the complete adopted theorem.
The compatibility wrapper now has no live or quarantined Lean importers.

## Old

The entire compatibility module was:

```lean
module

public import WeilConjectures.RingTheory.ResidueFieldProjectiveDimension

/-!
Compatibility import for the adopted source theorem. Its complete proof and mathematical
dependencies remain in the source module imported above.
-/
```

## New

Withdraw `lean/Sheaf/RingTheory/ResidueFieldProjectiveDimension.lean` through
`deleted.txt`. Use `WeilConjectures.RingTheory.ResidueFieldProjectiveDimension`
directly. The node `lem-weil-pbc-residue-field-pd-le-krull-dimension` retains its
adopted module, file, declaration, and verbatim statement; only its Lean note changes.
No upstream file, target statement, definition, or mathematical proof is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ResidueFieldProjectiveDimension | K4 | Withdraw the unused reexport. |
| Sheaf.RingTheory.RegularLocalOfFiniteGlobalDimension | unclaimed | Historical inventory consumer is already absent; no file is changed. |
| WeilConjectures.RingTheory.RegularLocalOfFiniteGlobalDimension | unclaimed | Actual DAG parent imports the adopted theorem directly; compiled unchanged. |

`tools/downstream.py Sheaf.RingTheory.ResidueFieldProjectiveDimension` reports
no downstream modules. Direct import searches in `lean/` and `quarantine/`
likewise find none. The only DAG parent is
`lem-weil-pbc-finite-gl-dim-regular-local`; its attachment is already the adopted
regular-local module. Its actual proof applies
`(Ring.residueField_projectiveDimension_le_ringKrullDim R hres).2 D hD`.
Thus the parent still uses the same theorem, including its bounded-resolution
conclusion; no DAG edge or unit realization is pruned.

The unchanged adopted consumer compiled through `lcompile.py` without warnings
(1.3 seconds). An independent scratch application of the full adopted signature
also compiled (1.0 second); `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for the adopted theorem. A recursive check
of project imports from that consumer found no Sheaf modules and no twin pairs.

## Status

landed 20261020T162545-L-3622023 2026-10-20 (merge of deliver/K4/Sheaf.RingTheory.ResidueFieldProjectiveDimension)
