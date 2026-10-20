# Field.nonempty_equiv_brauerGroup_galoisUnitsH2

## Reason

Retirement item in coord/retire-items.tsv, authorized by the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The local Sheaf module has no consumers.
The upstream twin supplies an actual equivalence with exactly the same source and target.
The local existence wrapper duplicates this construction and is no longer needed.

## Old

```lean
theorem nonempty_equiv_brauerGroup_galoisUnitsH2 (K : Type u) [Field K] :
    Nonempty (BrauerGroup.{u, u} K ≃ GaloisUnitsH2 K)
```

## New

Withdraw lean/Sheaf/FieldTheory/BrauerGaloisComparison.lean and redirect the existing
DAG node to Field.brauerGroupEquivGaloisUnitsH2 in
WeilConjectures.FieldTheory.BrauerGaloisComparison. Its existing type, with the section
parameters displayed, is:

```lean
noncomputable def brauerGroupEquivGaloisUnitsH2 (K : Type u) [Field K] :
    BrauerGroup.{u, u} K ≃ GaloisUnitsH2 K
```

The old theorem follows by `exact ⟨Field.brauerGroupEquivGaloisUnitsH2 K⟩`.
This implication compiled for arbitrary K and universe u through lcompile.py. The upstream
construction's axiom audit reports only propext, Classical.choice and Quot.sound.
The source library and target statements are untouched.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.FieldTheory.BrauerGaloisComparison | D3 | Withdraw the unused duplicate. |

`tools/downstream.py Sheaf.FieldTheory.BrauerGaloisComparison --uses
Field.nonempty_equiv_brauerGroup_galoisUnitsH2` reports zero downstream modules and
only the declaration itself as a name occurrence. An independent rg scan of lean/
finds no importing module or external use. The only live DAG attachment is
lem-sc-brauer-galois-units-comparison, redirected in this delivery. Historical
created.item fields in the scalar-defect nodes are preserved.

## Status

landed 20261020T135356-L-1816360 2026-10-20 (merge of deliver/D3/Sheaf.FieldTheory.BrauerGaloisComparison)
