# CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_summand

## Reason

The new proof needs local irreducibility attributes to avoid repeated unfolding
of chosen Hom-complex data and projection maps during elaboration. The delivery
checker treats added command text conservatively as an interface change and
requires this record. These attributes are explicitly local to this module.
The public theorem signature and visibility stay identical; no definition body,
target meaning, or exported reducibility attribute changes.

## Old

The theorem signature was:

```lean
theorem homTensorDegreewiseMap_iteratedDifferential_summand
    (K L M : CochainComplex Mod ℤ) (n t p q : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h
    (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (t + (n + 1)))) =
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1)))))
```

There were no local irreducibility commands in the original module.

## New

The theorem signature is unchanged, verbatim:

```lean
theorem homTensorDegreewiseMap_iteratedDifferential_summand
    (K L M : CochainComplex Mod ℤ) (n t p q : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h
    (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (t + (n + 1)))) =
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1)))))
```

The proof now uses these two module-local commands, placed before the helpers
and before the main theorem respectively:

```lean
attribute [local irreducible] homComplex homComplexFunctor
attribute [local irreducible] homTensorDegreewiseMap homTensorProjection
```

Only private helpers and proof-only imports are added to the existing module.
The two new public lemmas, `homTensorSummandPure_ext` and
`homTensor_pure_differentials`, are separately documented by their new DAG nodes.
The latter reuses `homTensorSectionMap_natural` from the existing
`Sheaf.Algebra.Homology.HomTensorSectionNaturality`; its proof remains sorry.
No new naturality declaration or node is delivered.

## Users

`tools/downstream.py --uses homTensorDegreewiseMap_iteratedDifferential_summand`
finds the following direct textual users. The wider transitive closure has no
changed statement or definition to adapt; local attributes do not propagate.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomTensorDifferentialSummand | Q2 | Its proof changes; signature identical. |
| Sheaf.Algebra.Homology.HomTensorDifferentialComponent | unclaimed | None; the imported theorem has its exact original type. No adaptation. |

No module held by another group is edited. No target statement or definition
changes and no target meaning review is reopened.

## Status

landed 20261013T100057-L-2477512 2026-10-13 (merge of deliver/Q2/Sheaf.Algebra.Homology.HomTensorDifferentialSummand)
