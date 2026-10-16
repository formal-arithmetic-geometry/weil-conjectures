# AlgebraicGeometry.ProEtale.finiteDiscreteSchemeRingIso and proEtTerminal

## Reason

Sectionwise kernel checks exceeded the 60-second limit when reducing concrete coefficient adjunction and pullback constructions. Expose the exact construction through proved equality APIs. This changes computation, not mathematical meaning. Witnesses are chosen only from proved statements specifying exact equality to the original construction. No hollow data, new assumptions, or axiom is introduced. All existing signatures and visibility are retained. Target meaning is unchanged; reviewers should check the equality APIs when renewing the definition review.

## Old

```lean
abbrev proEtTerminal (T : Scheme.{u}) : T.ProEt :=
  MorphismProperty.Over.mk ⊤ (𝟙 T) (by infer_instance)

instance (T : Scheme.{u}) : IsIso (proEtTerminal T).hom := by
  change IsIso (𝟙 T)
  infer_instance

instance (T : Scheme.{u}) : IsIso
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ.{u})).hom := by
  change IsIso (pullback.snd (𝟙 specZ.{u}) (toSpecZ T))
  infer_instance

noncomputable def proEtIsTerminal {T : Scheme.{u}} (U : T.ProEt) [IsIso U.hom] : IsTerminal U :=
  IsTerminal.ofUniqueHom
    (fun V ↦ MorphismProperty.Over.homMk (V.hom ≫ inv U.hom) (by simp) trivial)
    (by
      intro V m
      apply MorphismProperty.Comma.Hom.ext
      · apply (cancel_mono U.hom).mp
        simp
      · exact Subsingleton.elim _ _)

noncomputable def constantSchemeIso (T : Scheme.{u}) :
    constantSheaf (ProEt.topology T) Ab.{u + 1} ≅
      constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint T :=
  constantPullbackMonoidalIso
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T))
    (ProEt.topology specZ.{u}) (ProEt.topology T)
    (proEtIsTerminal (proEtTerminal specZ.{u}))
    (proEtIsTerminal
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
        (proEtTerminal specZ.{u}))) ≪≫
  Functor.isoWhiskerRight constantPointIso ((toSpecZ T)^*[Ab.{u + 1}]) ≪≫
  Functor.associator _ _ _

instance (T : Scheme.{u}) : NatTrans.IsMonoidal (constantSchemeIso T).hom := by
  dsimp only [constantSchemeIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open Scheme
open scoped CategoryTheory.Obj

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

noncomputable def finiteDiscreteSchemeRingIso (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        condensedRingObj (Profinite.continuousMapRingObj.{u} B) T :=
  (constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} B)) ≪≫
    (upperStarFromPoint T).mapIso eR

instance (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom] : IsMonHom (finiteDiscreteSchemeRingIso B T eR).hom := by
  let A := AddCommGrpCat.of (ULift.{u + 1} B)
  let S := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let P := upperStarFromPoint T
  let Q := constantSheaf (ProEt.topology T) Ab.{u + 1}
  let transfer (m : MonObj (S.obj A)) : MonObj (P.obj (S.obj A)) :=
    @Functor.monObjObj _ _ _ _ _ _ P _ _ m
  have hS := constantSheafRingMonObj (coherentTopology Profinite.{u}) (ULift.{u + 1} B)
  have hQ := constantSheafRingMonObj (ProEt.topology T) (ULift.{u + 1} B)
  let mS := Sheaf.monObj_presheafToSheaf_obj (coherentTopology Profinite.{u})
    (((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  let mQ := Sheaf.monObj_presheafToSheaf_obj (ProEt.topology T)
    (((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  have hi : @IsMonHom _ _ _ (P.obj (S.obj A)) (Q.obj A)
      (transfer mS) mQ ((constantSchemeIso T).inv.app A) :=
    IsMonHom.of_eq
      (h₁ := transfer (S.monObjObj A)) (h₂ := Q.monObjObj A)
      ((constantSchemeIso T).inv.app A) (congrArg transfer hS) hQ
      (hf := Functor.isMonHom_compAlgHom S P (constantSchemeIso T).inv A)
  have hh := monHomInvExplicit (transfer mS) mQ ((constantSchemeIso T).app A).symm hi
  have hmap : IsMonHom (P.map eR.hom) := inferInstance
  dsimp only [finiteDiscreteSchemeRingIso, Iso.trans_hom, Functor.mapIso_hom]
  exact monHomCompExplicit mQ (transfer mS) _
    ((constantSchemeIso T).hom.app A) (P.map eR.hom) hh hmap
```

## New

```lean
/-- The identity object is an explicit terminal pro-etale object.
The equality condition determines the witness uniquely. -/
theorem proEtTerminal_exists (T : Scheme.{u}) :
    ∃ W : T.ProEt, W = MorphismProperty.Over.mk ⊤ (𝟙 T) (by infer_instance) :=
  ⟨_, rfl⟩

/-- A terminal object, kept behind its equality API to avoid reducing iterated pullbacks
of the identity scheme during kernel checks of section comparisons. The defining theorem
specifies the exact identity object, so this choice carries no arbitrary data. -/
noncomputable def proEtTerminal (T : Scheme.{u}) : T.ProEt :=
  Classical.choose (proEtTerminal_exists T)

/-- The terminal object is exactly the identity scheme over itself. -/
theorem proEtTerminal_eq (T : Scheme.{u}) :
    proEtTerminal T = MorphismProperty.Over.mk ⊤ (𝟙 T) (by infer_instance) :=
  Classical.choose_spec (proEtTerminal_exists T)

instance (T : Scheme.{u}) : IsIso (proEtTerminal T).hom := by
  rw [proEtTerminal_eq]
  change IsIso (𝟙 T)
  infer_instance

instance (T : Scheme.{u}) : IsIso
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ.{u})).hom := by
  rw [proEtTerminal_eq]
  change IsIso (pullback.snd (𝟙 specZ.{u}) (toSpecZ T))
  infer_instance

noncomputable def proEtIsTerminal {T : Scheme.{u}} (U : T.ProEt) [IsIso U.hom] : IsTerminal U :=
  IsTerminal.ofUniqueHom
    (fun V ↦ MorphismProperty.Over.homMk (V.hom ≫ inv U.hom) (by simp) trivial)
    (by
      intro V m
      apply MorphismProperty.Comma.Hom.ext
      · apply (cancel_mono U.hom).mp
        simp
      · exact Subsingleton.elim _ _)

noncomputable def constantSchemeIso (T : Scheme.{u}) :
    constantSheaf (ProEt.topology T) Ab.{u + 1} ≅
      constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint T :=
  constantPullbackMonoidalIso
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T))
    (ProEt.topology specZ.{u}) (ProEt.topology T)
    (proEtIsTerminal (proEtTerminal specZ.{u}))
    (proEtIsTerminal
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
        (proEtTerminal specZ.{u}))) ≪≫
  Functor.isoWhiskerRight constantPointIso ((toSpecZ T)^*[Ab.{u + 1}]) ≪≫
  Functor.associator _ _ _

instance (T : Scheme.{u}) : NatTrans.IsMonoidal (constantSchemeIso T).hom := by
  dsimp only [constantSchemeIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open Scheme
open scoped CategoryTheory.Obj

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

theorem finiteDiscreteSchemeRingIso_exists (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    ∃ e : (    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        condensedRingObj (Profinite.continuousMapRingObj.{u} B) T), e =
      (constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} B)) ≪≫
    (upperStarFromPoint T).mapIso eR :=
  ⟨_, rfl⟩

/-- The explicit constant coefficient comparison, accessed through its equality API.
This construction chooses the unique value specified by a proved equality, so it adds
no arbitrary coefficient identification. -/
noncomputable def finiteDiscreteSchemeRingIso (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        condensedRingObj (Profinite.continuousMapRingObj.{u} B) T :=
  Classical.choose (finiteDiscreteSchemeRingIso_exists B T eR)

theorem finiteDiscreteSchemeRingIso_eq (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    finiteDiscreteSchemeRingIso B T eR =
      (constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} B)) ≪≫
    (upperStarFromPoint T).mapIso eR :=
  Classical.choose_spec (finiteDiscreteSchemeRingIso_exists B T eR)

instance (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom] : IsMonHom (finiteDiscreteSchemeRingIso B T eR).hom := by
  let A := AddCommGrpCat.of (ULift.{u + 1} B)
  let S := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let P := upperStarFromPoint T
  let Q := constantSheaf (ProEt.topology T) Ab.{u + 1}
  let transfer (m : MonObj (S.obj A)) : MonObj (P.obj (S.obj A)) :=
    @Functor.monObjObj _ _ _ _ _ _ P _ _ m
  have hS := constantSheafRingMonObj (coherentTopology Profinite.{u}) (ULift.{u + 1} B)
  have hQ := constantSheafRingMonObj (ProEt.topology T) (ULift.{u + 1} B)
  let mS := Sheaf.monObj_presheafToSheaf_obj (coherentTopology Profinite.{u})
    (((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  let mQ := Sheaf.monObj_presheafToSheaf_obj (ProEt.topology T)
    (((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  have hi : @IsMonHom _ _ _ (P.obj (S.obj A)) (Q.obj A)
      (transfer mS) mQ ((constantSchemeIso T).inv.app A) :=
    IsMonHom.of_eq
      (h₁ := transfer (S.monObjObj A)) (h₂ := Q.monObjObj A)
      ((constantSchemeIso T).inv.app A) (congrArg transfer hS) hQ
      (hf := Functor.isMonHom_compAlgHom S P (constantSchemeIso T).inv A)
  have hh := monHomInvExplicit (transfer mS) mQ ((constantSchemeIso T).app A).symm hi
  have hmap : IsMonHom (P.map eR.hom) := inferInstance
  rw [finiteDiscreteSchemeRingIso_eq]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  exact monHomCompExplicit mQ (transfer mS) _
    ((constantSchemeIso T).hom.app A) (P.map eR.hom) hh hmap
```

## Users

All modules listed by tools/downstream.py --uses are included below. Four unclaimed consumers replace explicit unfolding with the defining equation; two also rewrite that equation before using an adjunction square. Their original failures and adapted compilations are recorded in the report.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientExchangeFromComparisons | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientSections | D3 | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteSchemeRing | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Exact equality preserves all statements and mathematical constructions. |

| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Exact equality preserves the coefficient comparison and its isomorphism instances; statements unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Exact equality preserves the coefficient comparison and its isomorphism instances; statements unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Exact equality preserves the coefficient comparison and its isomorphism instances; statements unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Exact equality preserves the coefficient comparison and its isomorphism instances; statements unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Exact equality preserves the coefficient comparison and its isomorphism instances; statements unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientTerminal | D3 | Exact equality preserves the coefficient comparison and its isomorphism instances; statements unchanged. |

## Status

landed 20261016T171806-L-1680950 2026-10-16 (merge of deliver/D3/Sheaf.Paper.FiniteDiscreteCoefficientSections)
