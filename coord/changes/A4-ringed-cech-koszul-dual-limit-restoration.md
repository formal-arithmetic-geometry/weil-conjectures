# CategoryTheory.ringed_cech_koszul_dual_limit

## Reason

Restore the quarantined module assigned by coord/rework.tsv. Its compiler error names
`telescopeShiftColimit` and `telescopeToColimit`: the retired Sheaf telescope module
exports neither. The source module supplies the proved comparison and the canonical
shift name. This is exactly the restoration migration documented in
coord/changes/retire-telescope-colimit-a2.md. Group A4 holds this rework item.

## Old

```lean
public import Sheaf.Algebra.Homology.TelescopeColimit
theorem ringed_cech_koszul_dual_limit :
    (∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) ∧
      ∃ t : CochainComplex.mappingCone
          (CochainComplex.telescopeShiftColimit O (ringedKoszulDiagram O r b)) ⟶
            (ringedExtendedCech O r b).1,
        CochainComplex.mappingCone.inr _ ≫ t =
          CochainComplex.telescopeToColimit O (ringedKoszulDiagram O r b) ≫ alpha.hom ∧
        QuasiIso t) ∧
    (∀ m : ℕ, CochainComplex.IsAcyclicTensorKFlat ((ringedKoszulDualTower O r b).obj (op m))) ∧
    Nonempty (RingedKoszulCechComparison O r b)
```

## New

```lean
public import WeilConjectures.Algebra.Homology.TelescopeColimit
theorem ringed_cech_koszul_dual_limit :
    (∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) ∧
      ∃ t : CochainComplex.mappingCone
          (CochainComplex.telescopeColimitShift O (ringedKoszulDiagram O r b)) ⟶
            (ringedExtendedCech O r b).1,
        CochainComplex.mappingCone.inr _ ≫ t =
          CochainComplex.telescopeToColimit O (ringedKoszulDiagram O r b) ≫ alpha.hom ∧
        QuasiIso t) ∧
    (∀ m : ℕ, CochainComplex.IsAcyclicTensorKFlat ((ringedKoszulDualTower O r b).obj (op m))) ∧
    Nonempty (RingedKoszulCechComparison O r b)
```

The former abbreviation `telescopeShiftColimit O E` expanded to
`telescopeColimitShift O E`. Thus this spelling change preserves the elaborated
type, actual mapping cone, comparison map and its canonicality equation. No definition,
hypothesis or conclusion changes, and no target statement needs semantic re-review.
All other signatures, data, imports and proofs are preserved verbatim. The DAG Lean
attachment records the new spelling; its mathematical statement and dependencies stay.

## Users

A search of lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf finds no active Lean
importer and precisely the following quarantined importers. tools/downstream.py reports
"unknown module(s)" because the item itself is quarantined; the explicit archive search
therefore supplies the consumer list. No consumer needs an adaptation: the changed name
was an abbreviation of the same source expression, and the restored module reexports
its defining source module. Quarantined files remain untouched, with their attachments
and dependencies preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedCechKoszulDualLimit | A4 | Restore all declarations and proofs, migrate telescope import and shift spelling. |
| Sheaf.CategoryTheory.RingedKoszulCompletionReflector | quarantined; not adapted | Same exported declarations and definitionally equal theorem type. |
| Sheaf.Paper.RingedPushforwardCompletion | quarantined; not adapted | Same exported declarations and definitionally equal theorem type. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | quarantined; not adapted | Same exported declarations and definitionally equal theorem type. |

The replacement uses the identical telescope for all sequences, including the empty
Koszul list, zero sections, units and zero coefficient rings. The existing empty-list
unit proof and all normalized restriction coherence proofs compile unchanged.
No source-library file is changed. No forced adaptations or new proof obligations.

## Status

landed 20261020T161729-L-3528690 2026-10-20 (merge of deliver/A4/Sheaf.CategoryTheory.RingedCechKoszulDualLimit)

Validation: restored module compiles cleanly through lcompile.py in 11.7 seconds.
Zero holes before restoration, zero holes after restoration; no proof claims added.
