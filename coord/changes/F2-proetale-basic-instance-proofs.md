# Proofs of the Basic coefficient-site instances

## Reason

The stage-3 preflight classifies changes to these seven instance bodies as interface
changes. Each existing signature, universe, visibility and public import is unchanged.
All seven instances are propositions; proof irrelevance preserves every downstream
instance argument. The proof bodies now use only the permitted axioms.
No data definition is changed, and no other module is adapted.

## Old

```lean
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} :=
  sorry
```

```lean
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) :=
  sorry
```

```lean
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} :=
  sorry
```

```lean
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F :=
  sorry
```

```lean
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) :=
  sorry
```

```lean
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) :=
  sorry
```

```lean
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom :=
  sorry
```

## New

```lean
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} := by
  infer_instance
```

```lean
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) := by
  let e : CommRingCat.of (LocallyConstant S (ULift.{u} ℤ)) ≅
      CommRingCat.of (LocallyConstant S ℤ) :=
    (LocallyConstant.congrRightRingEquiv ULift.ringEquiv).toCommRingCatIso
  have : WeaklyEtale
      (Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (LocallyConstant S (ULift.{u} ℤ))))) := by
    infer_instance
  rwa [specULiftZIsTerminal.hom_ext
    (Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (LocallyConstant S (ULift.{u} ℤ)))))
    (toSpecZ (profiniteToScheme.obj S))] at this
```

```lean
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} := by
  have h := (Adjunction.adjunctionOfEquivLeft profiniteLocallyConstantHomEquiv
    profiniteLocallyConstantHomEquiv_naturality).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits profiniteToCommRingCatOp.{u} := inferInstance
  have : PreservesFiniteLimits profiniteToScheme.{u} := by
    unfold profiniteToScheme
    infer_instance
  have : (Over.forget specZ.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
  have : PreservesFiniteLimits
      ((profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) ⋙ Over.forget specZ) :=
    inferInstanceAs (PreservesFiniteLimits profiniteToScheme.{u})
  have : PreservesFiniteLimits (profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Over.forget specZ)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.ProEt.forget specZ)
```

```lean
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F := by
  infer_instance
```

```lean
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) := by
  unfold pointUpperStar
  infer_instance
```

```lean
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) := by
  unfold pointUpperStar
  infer_instance
```

```lean
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ toSpecZ Y))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y)).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  have hr : NatTrans.IsMonoidal (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).hom := by
    unfold lowerStarComp
    infer_instance
  have hc : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv :=
    isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).inv
  have he (g g' : X ⟶ specZ.{u}) (h : g = g') : NatTrans.IsMonoidal
      (eqToIso (congrArg (upperStar Ab.{u + 1}) h)).hom := by
    subst g'
    exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
  have := he (f ≫ toSpecZ Y) (toSpecZ X) (comp_toSpecZ f)
  unfold upperStarFromPointComp
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance
```

The finite-limit proof uses four private, fully proved helpers in the item module.
The seven added imports are ordinary proof imports, not public imports. Two of those
imports were removed after the second-reading import minimization; the final module
retains five ordinary proof imports.

## Users

For each of the seven declarations, `tools/downstream.py --uses` finds only the
declaration in the item itself. The complete transitive importer list is included
below as well, since instances can be used implicitly without textual mentions.
The holders are those recorded locally when this record was written.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` | F2 | All eight proof holes filled; no signature or visibility changes. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse` | B2 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover` | C3 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover` | B3 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` | C2 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` | C3 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover` | C4 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.AdicCompletionReduction` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CompletionMap` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedPointBasisEvaluation` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | C1 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedQcqsPushforwardContinuity` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.GeometricFieldProEtaleEvaluation` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.IntrinsicKoszulCompletion` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.KoszulQuotientLimit` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.PointLanAffineEvaluation` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.ProEtalePointComponentsMaps` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.ProEtaleSheafificationWcontractibleSections` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.ProfinitePointPullback` | B4 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Paper.ProfiniteTestObjectFunctor` | F1 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.RingTheory.BoundedWContractibleExtension` | D3 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `Sheaf.Topology.BoundedExtremallyDisconnectedCover` | F4 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `TargetsCheck` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | A2 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | E4 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | A2 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | E4 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | F3 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | F3 | No adaptation: signatures, public imports and instance propositions are unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` | unclaimed | No adaptation: signatures, public imports and instance propositions are unchanged. |

## Status

landed 20261015T154210-L-164197 2026-10-15 (merge of deliver/F2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic)
