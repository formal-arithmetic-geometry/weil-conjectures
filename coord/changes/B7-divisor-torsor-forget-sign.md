# AlgebraicGeometry.Etale.divisor_torsor_boundary_signs

## Reason

The raw lifting cocycle has negative Ext-normalized forgetful image. The original theorem required both its positive representative and a positive Ext forgetful image. RelativeTorsorForgetNormalization.relativeFrameClass_forget proves the missing minus sign, using FirstResolutionExtensionClass.extMk_firstCycles. The corrected theorem keeps every coordinate and boundary requirement and negates its forgetful image. No existing definition or target statement changes. This is a sign correction, not a proof of the incompatible original assertion.

## Old

```lean
theorem divisor_torsor_boundary_signs :
    ∃ e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1,
    ((∀ T W G I,
      e T W G I (Quotient.mk _
        ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op (Scheme.Etale.mk W.ι))) 0⟩) = 0) ∧
    (∀ T W G I (c : ResolutionSectionCanonicalComparison G I)
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)),
      relativeForgetH1 T W G I c (e T W G I (Quotient.mk _ P)) =
        Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
          (Quotient.mk _ P.1)) ∧
    (∀ (T : Scheme.{u}) (W : T.Opens)
      (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : G ⟶ G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.Hom J f) (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
      (Q : Sheaf.Torsor G') (q : Sheaf.Torsor.ContractedProductPresentation.{u, u} T f P.1 Q),
      HomologicalComplex.homologyMap
          (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1
          (e T W G I (Quotient.mk _ P)) =
        e T W G' J (Quotient.mk _ ⟨Q, q.quotient (op (Scheme.Etale.mk W.ι)) P.2 0⟩)) ∧
    (∀ (T T' : Scheme.{u}) (h : T' ⟶ T) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.cocomplex ⟶
        ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
      (_ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)) (Q : Sheaf.Torsor G')
      (b : P.1.sheaf.obj ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
      (_hb : ∀ (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.1.sheaf.obj.obj A),
        b.app A (P.1.vadd A g t) =
          Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj A.unop))
            (f.hom.app A g) (b.app A t)),
      HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) 1
          (e T W G I (Quotient.mk _ P)) =
        e T' (h ⁻¹ᵁ W) G' J (Quotient.mk _
          ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
            (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩))) ∧
    DivisorTorsorBoundarySigns e
```

## New

```lean
theorem divisor_torsor_boundary_signs :
    ∃ e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1,
    ((∀ T W G I,
      e T W G I (Quotient.mk _
        ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op (Scheme.Etale.mk W.ι))) 0⟩) = 0) ∧
    (∀ T W G I (c : ResolutionSectionCanonicalComparison G I)
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)),
      -relativeForgetH1 T W G I c (e T W G I (Quotient.mk _ P)) =
        Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
          (Quotient.mk _ P.1)) ∧
    (∀ (T : Scheme.{u}) (W : T.Opens)
      (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : G ⟶ G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.Hom J f) (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
      (Q : Sheaf.Torsor G') (q : Sheaf.Torsor.ContractedProductPresentation.{u, u} T f P.1 Q),
      HomologicalComplex.homologyMap
          (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1
          (e T W G I (Quotient.mk _ P)) =
        e T W G' J (Quotient.mk _ ⟨Q, q.quotient (op (Scheme.Etale.mk W.ι)) P.2 0⟩)) ∧
    (∀ (T T' : Scheme.{u}) (h : T' ⟶ T) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.cocomplex ⟶
        ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
      (_ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)) (Q : Sheaf.Torsor G')
      (b : P.1.sheaf.obj ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
      (_hb : ∀ (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.1.sheaf.obj.obj A),
        b.app A (P.1.vadd A g t) =
          Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj A.unop))
            (f.hom.app A g) (b.app A t)),
      HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) 1
          (e T W G I (Quotient.mk _ P)) =
        e T' (h ⁻¹ᵁ W) G' J (Quotient.mk _
          ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
            (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩))) ∧
    DivisorTorsorBoundarySigns e
```

Private canonical instances and the abstract cone/cycle API reduce elaboration work. The existing public definitions and the public theorem signature retain their original canonical instances. No new public alias or global instance is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns | B7 | Corrected and proved; no external Lean callers exist. |

The downstream declaration-use audit finds no importing users. Four DAG citers are audited in the node statement_change: SupportedYonedaLocalization uses the unchanged coefficient boundary computation; CartierGysinKummerBoundary and TraitGysinResidue use the unchanged localization sign; PurityDivisorClass uses the unchanged raw representatives and already distinguishes them from Yoneda normalization. No quarantined parent is withdrawn or modified. The unit record has no realized nodes for this item, and its route is preserved.

## Status

landed 20261020T221051-L-4140253 2026-10-20 (merge of deliver/B7/Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns)
