# AlgebraicGeometry.ProEtale.CondensedRing.hasProjectionFormula_openImmersion

## Reason

The existing `sorry` is replaced by a complete proof. The declaration still has exactly
its original proposition type, universe, binders, visibility, and instance registration.
No statement, definition, or public import is changed. Proof irrelevance makes the old
and new proofs definitionally equal wherever this instance is used. Consequently the
meaning of no target or downstream definition changes and no adaptation is required.

The record is supplied because `tools/leanindex.py:interface` conservatively compares the
whole body of every `instance`, including Prop-valued instances. This makes stage-3
preflight require a change record for this proof-only edit. No tool was modified.

## Old

```lean
instance hasProjectionFormula_openImmersion :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).HasProjectionFormula :=
  sorry
```

## New

```lean
instance hasProjectionFormula_openImmersion :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).HasProjectionFormula := by
  refine ⟨fun L M ↦ ?_⟩
  let A := Ab.{u + 1}
  let l : U.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤
    (inferInstance : WeaklyEtale j)
  have : MorphismProperty.IsStableUnderComposition
      (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : l.Full := MorphismProperty.Over.full_map (P := @WeaklyEtale) (Q := ⊤) (f := j) _
  have : l.Faithful :=
    MorphismProperty.Over.faithful_map (P := @WeaklyEtale) (Q := ⊤) (f := j) _
  let adj₀ := ProEtale.openImmersionLowerShriekAdjunction A j
  have : IsIso adj₀.unit :=
    (ProEtale.openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  have : (j)_!open[A].Full := adj₀.fullyFaithfulLOfIsIsoUnit.full
  have : (j)_!open[A].Faithful := adj₀.fullyFaithfulLOfIsIsoUnit.faithful
  let adj := ProEtale.openImmersionLowerShriekUpperStarAdjunction A j
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  -- Tensoring a presheaf extension by zero still vanishes away from the open.
  let R := l.op.lan.obj M.obj ⊗ L.obj
  have hR (W : X.ProEtᵒᵖ) (hW : IsEmpty (CostructuredArrow l.op W)) :
      IsZero (R.obj W) := by
    exact ((l.op.isInitialLanObjObj M.obj hW).isInitialObj
      (tensorRight (L.obj.obj W))).isZero
  have : IsIso ((l.op.lanAdjunction A).counit.app R) :=
    Functor.isIso_lanAdjunction_counit_app_of_isZero _
      (SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap
        (inferInstance : WeaklyEtale j)) R hR
  -- Sheafification transports this support calculation to sheaves.
  let eLan : l.op.lan ⋙ presheafToSheaf (Scheme.ProEt.topology X) A ≅
      presheafToSheaf (Scheme.ProEt.topology U) A ⋙ (j)_!open[A] :=
    (((l.op.lanAdjunction A).comp (sheafificationAdjunction _ A)).leftAdjointUniq
      ((sheafificationAdjunction _ A).comp adj₀))
  let eTensor : (j)_!open[A].obj M ⊗ L ≅
      (presheafToSheaf (Scheme.ProEt.topology X) A).obj R :=
    whiskerLeftIso _ (asIso ((sheafificationAdjunction _ A).counit.app L)).symm ≪≫
      Functor.Monoidal.μIso (presheafToSheaf _ A) _ _
  let eSupport : (presheafToSheaf (Scheme.ProEt.topology X) A).obj R ≅
      (j)_!open[A].obj ((presheafToSheaf (Scheme.ProEt.topology U) A).obj (l.op ⋙ R)) :=
    (presheafToSheaf _ A).mapIso
      (asIso ((l.op.lanAdjunction A).counit.app R)).symm ≪≫ eLan.app _
  -- The target is in the essential image of the fully faithful left adjoint.
  have : IsIso (adj.counit.app (L ⊗ (j)_!open[A].obj M)) :=
    adj.isIso_counit_app_of_iso ((β_ L ((j)_!open[A].obj M)) ≪≫ eTensor ≪≫ eSupport)
  change IsIso (adj.projectionFormulaMap L M)
  rw [Adjunction.projectionFormulaMap, Adjunction.homEquiv_counit]
  infer_instance
```

## Users

`tools/downstream.py` reports the following 41 transitively importing modules. Its
`--uses hasProjectionFormula_openImmersion` search finds no textual user outside the
item itself. All users retain the same statements and definitions by proof irrelevance;
none is edited or requires an adaptation. Holders are from the local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse | B2 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CompletionMap | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Same Prop instance type and visibility; no adaptation. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | Same Prop instance type and visibility; no adaptation. |
| Sheaf.Topology.BoundedExtremallyDisconnectedCover | F4 | Same Prop instance type and visibility; no adaptation. |
| TargetsCheck | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | E4 | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | A2 | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | E4 | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | Same Prop instance type and visibility; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same Prop instance type and visibility; no adaptation. |

## Status

landed 20261015T154211-L-164399 2026-10-15 (merge of deliver/F3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs)
