# Tensor-pullback proof completions used by the Padic Tor criterion

## Reason

The restored criterion needs naturality of the ordinary tensor comparison for its kernel descent. Complete three existing proof holes in this unclaimed dependency, preserving every declaration signature, attribute, visibility, definition and public import. The preadditive and total-comparison proofs support its derived-tensor interface, which the retained local torsion argument also needs. No consumer adaptation is necessary.

## Old

```lean
theorem proEtaleTensorPreadditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    @MonoidalPreadditive (proEtaleRingModules X R) _ _
      (SheafOfModules.monoidalCategory R) := sorry
```

```lean
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
            ((proEtaleRingModulePullback f R S c).map z) := sorry
```

```lean
theorem proEtaleTensorPullbackTotal_isIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    IsIso (proEtaleTensorPullbackTotal f R S c P Q) := sorry
```

## New

The signatures above stay verbatim. Their proof bodies are:

```lean
theorem proEtaleTensorPreadditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    @MonoidalPreadditive (proEtaleRingModules X R) _ _
      (SheafOfModules.monoidalCategory R) := by
  exact SheafOfModules.cochainModulesPreadditive R
```

```lean
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
            ((proEtaleRingModulePullback f R S c).map z) := by
  exact (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).1 M M' N N' v z
```

```lean
theorem proEtaleTensorPullbackTotal_isIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    IsIso (proEtaleTensorPullbackTotal f R S c P Q) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  exact tensorPullbackTotal_isIso (proEtaleRingModulePullback f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z)
    (proEtaleRingModuleDirectImage f R S c) (proEtaleRingModuleAdjunction f R S c) P Q
```

A private proof import of `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` supplies the proved universe-independent preadditivity. The old long line in `proEtaleFlatRepresentatives` is wrapped, with the expression unchanged.

## Users

The declaration-use search was run for all three declarations. Their direct users are below; the module has 412 transitive downstream modules, all with unchanged interfaces and proof-independent behavior.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleCanonicalTensorPullback | unclaimed | Three theorem proofs completed; no interface change. |
| Sheaf.Paper.ProEtaleProjectionFormulaArrows | unchanged; not adapted | Identical signatures and definitional data. |
| Sheaf.Paper.PerfectProjectionFormula | unchanged; not adapted | Identical naturality signature. |
| Sheaf.Paper.AdicTorFlatCriterion | G1 | Restored item uses naturality for kernel descent. |

## Status

landed 20261020T235559-L-1191967 2026-10-20 (merge of deliver/G1/Sheaf.Paper.AdicTorFlatCriterion)
