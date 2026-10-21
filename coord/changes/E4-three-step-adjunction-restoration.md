# CategoryTheory.Adjunction.threeStepComparison

## Reason

Restore the assigned quarantined module to its recorded Lean path. The row in
coord/rework.tsv records a cluster-restore revert at 5f7b33eac on 2026-10-20,
not a withdrawal of the mathematics. The archived module has a complete proof
and compiles against the current shared dependencies. No definition repair or
new proof hole is needed. Its public import and full declaration are preserved.

## Old

The live module is absent. The quarantined declaration to restore is:

```lean
theorem threeStepComparison
    (θ : G ⋙ V ≅ U ⋙ H) (θe : Ge ⋙ Ve ≅ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (δ : R ⋙ T₁ ≅ T₂ ⋙ Re) (δ' : S ⋙ T₃ ≅ T₄ ⋙ Se)
    (hunit : ∀ K, T₃.map (b.unit.app K) ≫ δ'.hom.app (V.obj K) ≫
      Se.map (αV.hom.app K) = be.unit.app (T₃.obj K))
    (hcounit : ∀ K, Ue.map (δ.hom.app K) ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hcube : ∀ K, T₄.map (θ.hom.app K) ≫ αH.hom.app (U.obj K) ≫
        He.map (αU.hom.app K) =
      αV.hom.app (G.obj K) ≫ Ve.map (αG.hom.app K) ≫ θe.hom.app (T₁.obj K))
    (K : C₂) :
    Nonempty (FiniteDiscreteThreeStepComparison
      (T₃.map (b.unit.app (G.obj (R.obj K))))
      (T₃.map (S.map (θ.hom.app (R.obj K))))
      (T₃.map (S.map (H.map (a.counit.app K))))
      (be.unit.app (Ge.obj (Re.obj (T₂.obj K))))
      (Se.map (θe.hom.app (Re.obj (T₂.obj K))))
      (Se.map (He.map (ae.counit.app (T₂.obj K)))))
```

## New

The same declaration, with its complete archived proof, restored at
lean/Sheaf/CategoryTheory/ThreeStepAdjunctionComparison.lean:

```lean
theorem threeStepComparison
    (θ : G ⋙ V ≅ U ⋙ H) (θe : Ge ⋙ Ve ≅ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (δ : R ⋙ T₁ ≅ T₂ ⋙ Re) (δ' : S ⋙ T₃ ≅ T₄ ⋙ Se)
    (hunit : ∀ K, T₃.map (b.unit.app K) ≫ δ'.hom.app (V.obj K) ≫
      Se.map (αV.hom.app K) = be.unit.app (T₃.obj K))
    (hcounit : ∀ K, Ue.map (δ.hom.app K) ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hcube : ∀ K, T₄.map (θ.hom.app K) ≫ αH.hom.app (U.obj K) ≫
        He.map (αU.hom.app K) =
      αV.hom.app (G.obj K) ≫ Ve.map (αG.hom.app K) ≫ θe.hom.app (T₁.obj K))
    (K : C₂) :
    Nonempty (FiniteDiscreteThreeStepComparison
      (T₃.map (b.unit.app (G.obj (R.obj K))))
      (T₃.map (S.map (θ.hom.app (R.obj K))))
      (T₃.map (S.map (H.map (a.counit.app K))))
      (be.unit.app (Ge.obj (Re.obj (T₂.obj K))))
      (Se.map (θe.hom.app (Re.obj (T₂.obj K))))
      (Se.map (He.map (ae.counit.app (T₂.obj K)))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | E4 | Restore the assigned module and complete proof. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | quarantined; not adapted | Existing explicit specialization regains its imported theorem; interface unchanged. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | quarantined; not adapted | Existing proof import resolves again; no textual use of threeStepComparison. |

The source scan includes quarantine: the table lists both direct Lean importers.
CoefficientExchangeFromComparisons is the only direct use of threeStepComparison. DAG parents remain unchanged, including
lem-weil-pbc-coefficient-exchange-from-comparisons and sk-thm-properbasechange.
The live-only downstream.py reports the absent module as unknown, so this table
uses the actual live and quarantine source scan. The unchanged quarantined CoefficientExchangeFromComparisons was also tested
and reached its 60-second limit; this restoration introduces no definition or
interface delta against its archived dependency. No consumer compile success
is claimed. No consumer is delivered or changed. No target statement or definition changes meaning.

## Status

landed 20261021T021008-L-2689687 2026-10-21 (merge of deliver/E4/Sheaf.CategoryTheory.ThreeStepAdjunctionComparison)
