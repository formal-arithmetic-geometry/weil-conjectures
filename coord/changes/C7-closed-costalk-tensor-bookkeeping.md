# Tensor comparison proof bookkeeping

## Reason

The costalk projection argument uses these two currently unclaimed Sheaf modules.
Five existing proof holes are bookkeeping consequences of already proved library
APIs. Fill both tensor-preadditivity proofs from
`SheafOfModules.cochainModulesPreadditive`; extract ordinary naturality from the
selected witness's characterization; apply `CategoryTheory.tensorPullbackTotal_isIso`
to both total comparisons and their specified adjunctions. No statement,
non-theorem construction, attribute or public import changes. The only new
imports are private proof imports of `CochainTensorUniverses`.

## Old

These signatures are verbatim. Their proof bodies were `sorry`.

```lean
-- Sheaf.Paper.ProEtaleCanonicalTensorPullback
theorem proEtaleTensorPreadditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    @MonoidalPreadditive (proEtaleRingModules X R) _ _
      (SheafOfModules.monoidalCategory R)

-- Sheaf.Paper.ProEtaleCanonicalTensorPullback
theorem proEtaleOrdinaryTensorPullback_naturality
    (M M' N N' : proEtaleRingModules Y R) (v : M ⟶ M') (z : N ⟶ N') :
    (proEtaleRingModulePullback f R S c).map
        (((proEtaleOrdinaryTensor Y R).map v).app N ≫
          ((proEtaleOrdinaryTensor Y R).obj M').map z) ≫
        (proEtaleOrdinaryTensorPullback f R S c M' N').hom =
      (proEtaleOrdinaryTensorPullback f R S c M N).hom ≫
        ((proEtaleOrdinaryTensor X S).map
          ((proEtaleRingModulePullback f R S c).map v)).app
            ((proEtaleRingModulePullback f R S c).obj N) ≫
        ((proEtaleOrdinaryTensor X S).obj
          ((proEtaleRingModulePullback f R S c).obj M')).map
            ((proEtaleRingModulePullback f R S c).map z)

-- Sheaf.Paper.ProEtaleCanonicalTensorPullback
theorem proEtaleTensorPullbackTotal_isIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    IsIso (proEtaleTensorPullbackTotal f R S c P Q)

-- Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
theorem ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) _ _ (monoidalCategory R)

-- Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
theorem CanonicalRingedTensorComparison.total_isIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) :
    IsIso (k.total R S RI uInv I c L hobj P Q)
```

## New

Exactly the same five signatures. Their proofs now use the existing APIs above,
with no new theorem, axiom or hole. The two total-isomorphism proofs use the
specified left adjoints, so the coproduct comparison is invertible in every degree.
Only the existing long `proEtaleFlatRepresentatives` line is rewrapped for style;
its term is identical. The pro-etale total-isomorphism proof first unfolds only
`proEtaleTensorPullbackTotal` and scopes the existing transparency option to the
proof: this avoids expensive conversion through the actual operation constructors.
No compile limit was raised. The final all-files compile took 31.4 seconds for
this module, 40.3 seconds for the general comparison module, and under 10 seconds
for each costalk/projection module.

## Users

`tools/downstream.py` was run with all five declaration names. Its textual matches
include other namespaces; the table includes every reported module. Both edited
modules were unclaimed when copied. No module held by another group is edited,
and no consumer adaptation is required for a proof-only change.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProjectionMateExact` | T8 | No edit; identical public signatures and imports. |
| `Sheaf.Paper.RingedProjectionCoherenceData` | unclaimed | No edit; identical public signatures and imports. |
| `Sheaf.Paper.RingedProjectionTensorStructure` | unclaimed | No edit; identical public signatures and imports. |
| `Sheaf.Paper.RingedStrictTowerProjectionMorphism` | P3 | No edit; identical public signatures and imports. |
| `Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses` | unclaimed | Existing theorem proofs filled; public interface unchanged. |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` | unclaimed | No edit; identical public signatures and imports. |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | E6 | No edit; identical public signatures and imports. |
| `Sheaf.Paper.ringedProjectionFormula_totalization_right` | unclaimed | No edit; identical public signatures and imports. |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | unclaimed | No edit; identical public signatures and imports. |
| `Sheaf.Paper.ProEtaleCanonicalTensorPullback` | unclaimed | Existing theorem proofs filled; public interface unchanged. |
| `Sheaf.Paper.ProEtaleProjectionFormulaArrows` | unclaimed | No edit; identical public signatures and imports. |
| `Sheaf.Paper.PerfectProjectionFormula` | T7 | No edit; identical public signatures and imports. |

## Status

landed 20261020T211645-L-3484815 2026-10-20 (merge of deliver/C7/Sheaf.SixFunctors.ClosedCostalkDuality)
