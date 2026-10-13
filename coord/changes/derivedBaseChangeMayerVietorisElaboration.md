# derivedBaseChange_mayerVietoris_naturality canonical open comparison

## Reason

The paper uses canonical restriction/pullback comparisons. The old Lean statement picked independent witnesses from a bare Nonempty isomorphism theorem. It provided no unit, counit or nested-restriction coherence. On identical opens in the identity square such an unspecified witness can carry an arbitrary automorphism, so its correspondence with the adjunction units cannot be inferred from existence. For compilation, the six repeated Triangle.mk expressions are also written as calls to mvBaseChangeTriangle with the same arguments; unfolding its body recovers the previous canonical statement without logical change. Replace the three witnesses by explicit composites of the pinned derived pullback composition comparisons and the left-adjoint-uniqueness comparisons between open pullback and exact restriction. This corrects canonical data, adds no hypothesis and drops no component or connecting-square conclusion. No declaration of Challenge.lean changes. The targets do not mention this comparison data, and no target definition is changed.

Both obligation modules set both backward.isDefEq.respectTransparency options to false. The main module now sets both backward.isDefEq.respectTransparency options to true. The second reader compressed the six repeated triangle constructors using mvBaseChangeTriangle (a definitionally identical statement), cached local preadditive and finite-biproduct instances with let, and marked the four new canonical adjunction/comparison constructors irreducible for elaboration. Their bodies are unchanged and remain transparent to kernel reduction; the two private uniqueness identities explicitly unfold mvOpenPullbackIso. The artifact-writing main compile passed in 33.7 seconds. The component construction module sets both to true. Its derived adjunction definition binds the polymorphic composition families using `@Classical.choose`, avoiding premature specialization of implicit scheme arguments and repeating inference on the nested existential specification. Its three component constructors now have explicit result types, and the unit/counit proof applications name the adjunctions. These changes preserve the constructed canonical data and their types. The long main theorem retains maxHeartbeats 200000. The retained second-reading entry describes earlier option experiments; the settings here describe the current delivered files.


Reviewer X-00326 H4 repair supersedes the adjunction-constructor description above:
`mvDerivedPullbackAdjunction` is now an `abbrev` of the existing
`canonicalPullbackAdjunction` from the added public import
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`. The explicit duplicate body is
removed, and `def-pc-affine-global-hom-base-change-map` is added to the component node's
`stmt_deps`. This is definitionally the same adjunction; the exact old/new bodies and
local users are recorded in `mvDerivedPullbackAdjunctionReuse.md`.

## Old

```lean
theorem derivedBaseChange_mayerVietoris_naturality [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S'] (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) [QuasiCompact f] [QuasiSeparated f] (hsq : IsPullback g' f' f g) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X') (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K') (ψ : (derivedPullback g').obj K ⟶ K') (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X)) (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤) : ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι) (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι) (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣ schemeDerivedDirectImage (U ⊓ V).ι) (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧) (adjU' : (schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory ⊣ schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι) (adjV' : (schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory ⊣ schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι) (adjUV' : (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory ⊣ schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι) (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶ K'⟦(1 : ℤ)⟧), ∃ (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ) (csG : (schemeDerivedDirectImage f').CommShift ℤ), Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K)) (biprod.desc (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV K) (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV K))) δ ∈ distTriang (schemeDerivedCategory X) ∧ Triangle.mk (biprod.lift (adjU'.unit.app K') (adjV'.unit.app K')) (biprod.desc (schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))) adjU' adjUV' K') (-(schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))) adjV' adjUV' K'))) δ' ∈ distTriang (schemeDerivedCategory X') ∧ (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj ( Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K)) (biprod.desc (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV K) (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV K))) δ) ∈ distTriang (schemeDerivedCategory S') ∧ (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj ( Triangle.mk (biprod.lift (adjU'.unit.app K') (adjV'.unit.app K')) (biprod.desc (schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))) adjU' adjUV' K') (-(schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))) adjV' adjUV' K'))) δ') ∈ distTriang (schemeDerivedCategory S') ∧ ∃ φ : (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj ( Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K)) (biprod.desc (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV K) (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV K))) δ) ⟶ (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj ( Triangle.mk (biprod.lift (adjU'.unit.app K') (adjV'.unit.app K')) (biprod.desc (schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U))) adjU' adjUV' K') (-(schemeDerivedOpenDirectImageRestriction X' ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V))) adjV' adjUV' K'))) δ'), φ.hom₁ = schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫ (schemeDerivedDirectImage f').map ψ ∧ ∃ aU : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj ((schemeDerivedDirectImage U.ι).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj K)) ⟶ (schemeDerivedDirectImage f').obj ((schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory.obj K')), aU = schemeDerivedBaseChangeMap f f' g g' hsq.w ((schemeDerivedDirectImage U.ι).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj K)) ≫ (schemeDerivedDirectImage f').map ( schemeDerivedBaseChangeMap U.ι (g' ⁻¹ᵁ U).ι g' (g'.resLE U (g' ⁻¹ᵁ U) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl) ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ≫ (schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).map ( (Classical.choice (derivedPullback_openRestriction_iso g' (g' ⁻¹ᵁ U) U le_rfl)).inv.app K ≫ (schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory.map ψ)) ∧ ∃ aV : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj ((schemeDerivedDirectImage V.ι).obj ((schemeOpenRestriction X V).mapDerivedCategory.obj K)) ⟶ (schemeDerivedDirectImage f').obj ((schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory.obj K')), aV = schemeDerivedBaseChangeMap f f' g g' hsq.w ((schemeDerivedDirectImage V.ι).obj ((schemeOpenRestriction X V).mapDerivedCategory.obj K)) ≫ (schemeDerivedDirectImage f').map ( schemeDerivedBaseChangeMap V.ι (g' ⁻¹ᵁ V).ι g' (g'.resLE V (g' ⁻¹ᵁ V) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl) ((schemeOpenRestriction X V).mapDerivedCategory.obj K) ≫ (schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).map ( (Classical.choice (derivedPullback_openRestriction_iso g' (g' ⁻¹ᵁ V) V le_rfl)).inv.app K ≫ (schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory.map ψ)) ∧ ∃ aUV : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj ((schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K)) ⟶ (schemeDerivedDirectImage f').obj ((schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K')), aUV = schemeDerivedBaseChangeMap f f' g g' hsq.w ((schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K)) ≫ (schemeDerivedDirectImage f').map ( schemeDerivedBaseChangeMap (U ⊓ V).ι (g' ⁻¹ᵁ (U ⊓ V)).ι g' (g'.resLE (U ⊓ V) (g' ⁻¹ᵁ (U ⊓ V)) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl) ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ≫ (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).map ( (Classical.choice (derivedPullback_openRestriction_iso g' (g' ⁻¹ᵁ (U ⊓ V)) (U ⊓ V) le_rfl)).inv.app K ≫ (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.map ψ)) ∧ φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.fst = (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.fst ≫ aU ∧ φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.snd = (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.snd ≫ aV ∧ φ.hom₃ = aUV
```

## New

```lean
theorem derivedBaseChange_mayerVietoris_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤) :
    ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣ schemeDerivedDirectImage (U ⊓
        V).ι)
      (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧)
      (adjU' : (schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory ⊣ schemeDerivedDirectImage
        (g' ⁻¹ᵁ U).ι)
      (adjV' : (schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory ⊣ schemeDerivedDirectImage
        (g' ⁻¹ᵁ V).ι)
      (adjUV' : (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory ⊣
        schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι)
      (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj
        ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶ K'⟦(1 : ℤ)⟧),
    ∃ (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ)
      (csG : (schemeDerivedDirectImage f').CommShift ℤ),
      mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ ∈ distTriang (schemeDerivedCategory X) ∧
      mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ' ∈ distTriang (schemeDerivedCategory X') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj (
        mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ) ∈ distTriang (schemeDerivedCategory S') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj (
        mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ') ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ φ :
        (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj
          (mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ) ⟶
        (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj (
          mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ'),
        φ.hom₁ = schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫
          (schemeDerivedDirectImage f').map ψ ∧
        ∃ aU : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
            ((schemeDerivedDirectImage U.ι).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj
              K)) ⟶
          (schemeDerivedDirectImage f').obj
            ((schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ
              U)).mapDerivedCategory.obj K')),
          aU =
            schemeDerivedBaseChangeMap f f' g g' hsq.w
                ((schemeDerivedDirectImage U.ι).obj ((schemeOpenRestriction X
                  U).mapDerivedCategory.obj K)) ≫
              (schemeDerivedDirectImage f').map (
                schemeDerivedBaseChangeMap U.ι (g' ⁻¹ᵁ U).ι g'
                    (g'.resLE U (g' ⁻¹ᵁ U) le_rfl)
                    (Scheme.Hom.resLE_comp_ι g' le_rfl)
                    ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ≫
                  (schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).map (
                    (mvPullbackOpenRestrictionIso g' U).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory.map ψ)) ∧
        ∃ aV : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
            ((schemeDerivedDirectImage V.ι).obj ((schemeOpenRestriction X V).mapDerivedCategory.obj
              K)) ⟶
          (schemeDerivedDirectImage f').obj
            ((schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ
              V)).mapDerivedCategory.obj K')),
          aV =
            schemeDerivedBaseChangeMap f f' g g' hsq.w
                ((schemeDerivedDirectImage V.ι).obj ((schemeOpenRestriction X
                  V).mapDerivedCategory.obj K)) ≫
              (schemeDerivedDirectImage f').map (
                schemeDerivedBaseChangeMap V.ι (g' ⁻¹ᵁ V).ι g'
                    (g'.resLE V (g' ⁻¹ᵁ V) le_rfl)
                    (Scheme.Hom.resLE_comp_ι g' le_rfl)
                    ((schemeOpenRestriction X V).mapDerivedCategory.obj K) ≫
                  (schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).map (
                    (mvPullbackOpenRestrictionIso g' V).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory.map ψ)) ∧
        ∃ aUV : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
            ((schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓
              V)).mapDerivedCategory.obj K)) ⟶
          (schemeDerivedDirectImage f').obj
            ((schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U
              ⊓ V))).mapDerivedCategory.obj K')),
          aUV =
            schemeDerivedBaseChangeMap f f' g g' hsq.w
                ((schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓
                  V)).mapDerivedCategory.obj K)) ≫
              (schemeDerivedDirectImage f').map (
                schemeDerivedBaseChangeMap (U ⊓ V).ι (g' ⁻¹ᵁ (U ⊓ V)).ι g'
                    (g'.resLE (U ⊓ V) (g' ⁻¹ᵁ (U ⊓ V)) le_rfl)
                    (Scheme.Hom.resLE_comp_ι g' le_rfl)
                    ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ≫
                  (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).map (
                    (mvPullbackOpenRestrictionIso g' (U ⊓ V)).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.map ψ)) ∧
          φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.fst =
            (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.fst ≫ aU ∧
          φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.snd =
            (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.snd ≫ aV ∧
          φ.hom₃ = aUV
```

## Users

The declaration-name scan finds no call outside this module. No original downstream file requires adaptation. The complete earlier transitive import list is retained below, with the same conclusion: these are import-only users and no declaration use needs changed lines.



The table includes the complete transitive downstream list from
`tools/downstream.py`, together with the assigned module. The declaration-name search finds no use outside the assigned module; no forced adaptations are delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | C4 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | J1 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | V3 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | S2 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | G4 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | P2 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | T4 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | N3 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | H4 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | H4 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnion | C1 | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| TargetsCheck | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Canonical comparison correction; no theorem call; no adaptation. |


## Status

landed 20261013T142853-L-496277 2026-10-13 (merge of deliver/C4/Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris)
