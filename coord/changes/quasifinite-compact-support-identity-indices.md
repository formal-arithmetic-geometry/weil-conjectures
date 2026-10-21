# AlgebraicGeometry.Etale.quasifiniteCompactSupportExact

## Reason

The three old identity-consistency clauses used `HEq c d` to express that a
compactification of an arbitrary morphism coincides with an identity compactification.
This omits the target-scheme and morphism equalities. Lean's dependent elimination reports
`Failed to solve equation Compactification g = Compactification f`; even equal endpoints
leave the morphism index unidentified. `Compactification.noConfusion` itself requires the
index equalities as inputs. No counterexample to the mathematical theorem is claimed.

The correction packages the target scheme, morphism, and compactification together in a
dependent sum and uses equality of these packages. It states actual coincidence including
the indices and keeps the conclusion unchanged. It does not restrict any map, coefficient,
exactness, independence, composition, sum-extension, or identity-normalization assertion.
The literal old HEq-only encoding is not asserted to follow from the corrected one.
The changed conditions clarify the intended identity specialization in Stacks Tags 0F7I,
0F7J and 0GKM; the target statements in Challenge.lean are untouched.

## Old

```lean
theorem quasifiniteCompactSupportExact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (hhq : h.IsQuasiFinite) (ehq : e.IsQuasiFinite) :
    ∃ (L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃ (ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        L f ⟶ lowerStar (ModuleCat.{u + 1} A) f),
      ∃ (o : ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
          (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f],
          etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ L f),
      ∃ (hA : (L h).Additive),
      ∃ (hL : PreservesFiniteLimits (L h)),
      ∃ (hC : PreservesFiniteColimits (L h)),
      ∃ (eA : (L e).Additive),
      ∃ (eL : PreservesFiniteLimits (L e)),
      ∃ (eC : PreservesFiniteColimits (L e)),
      ∃ (heA : (L (h ≫ e)).Additive),
      ∃ (heL : PreservesFiniteLimits (L (h ≫ e))),
      ∃ (heC : PreservesFiniteColimits (L (h ≫ e))),
      ∃ (c_h : ∀ c : Compactification h,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC),
      ∃ (c_e : ∀ c : Compactification e,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L e) eA eL eC),
      ∃ (c_he : ∀ c : Compactification (h ≫ e),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (h ≫ e)) heA heL heC),
      ∃ (idA : ∀ (X : Scheme.{u}) [IsNoetherian X], (L (𝟙 X)).Additive),
      ∃ (idL : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteLimits (L (𝟙 X))),
      ∃ (idC : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteColimits (L (𝟙 X))),
      ∃ (c_id : ∀ (X : Scheme.{u}) [IsNoetherian X] (c : Compactification (𝟙 X)),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (𝟙 X)) (idA X) (idL X) (idC X)),
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (V : Y.Etale),
        Function.Injective (((ι f).app F).hom.app (Opposite.op V)) ∧
        (∀ s : F.obj.obj (Opposite.op
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)),
          (∃ t, (((ι f).app F).hom.app (Opposite.op V)) t = s) ↔
          ∃ T₀ : TopologicalSpace.Closeds
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left,
            (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
              (v₀ : Spec (.of Ω) ⟶
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left),
              v₀ default ∈ T₀ ↔
                (Scheme.pointSmallEtale
                  (v₀ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom)).toPresheafFiber
                    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
                    (Over.homMk v₀) F.obj s ≠ 0) ∧
            IsProper ((Scheme.IdealSheafData.vanishingIdeal T₀).subschemeι ≫
              pullback.fst V.hom f))) ∧
      (∀ c d : Compactification h,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_h d).hom = (c_h c).hom) ∧
      (∀ c d : Compactification e,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_e d).hom = (c_e c).hom) ∧
      (∀ c d : Compactification (h ≫ e),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_he d).hom = (c_he c).hom) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X] (c d : Compactification (𝟙 X)),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_id X d).hom = (c_id X c).hom) ∧
      (∀ (c : Compactification h) (d : Compactification (𝟙 V)),
        HEq c d → HEq (c_h c) (c_id V d)) ∧
      (∀ (c : Compactification e) (d : Compactification (𝟙 T)),
        HEq c d → HEq (c_e c) (c_id T d)) ∧
      (∀ (c : Compactification (h ≫ e)) (d : Compactification (𝟙 V)),
        HEq c d → HEq (c_he c) (c_id V d)) ∧
      (∃ σ : L h ⋙ L e ≅ L (h ≫ e),
        (∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          σ.hom.app F ≫ (ι (h ≫ e)).app F =
            (ι e).app ((L h).obj F) ≫
              (lowerStar (ModuleCat.{u + 1} A) e).map ((ι h).app F) ≫
              (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app F) ∧
        ((unboundedEtaleLowerShriekCompIso A h e ≪≫
          (rightDerivedLowerShriekIso A
            (HasCompactification.compactification (h ≫ e))).symm ≪≫
          c_he (HasCompactification.compactification (h ≫ e))) =
          (Functor.isoWhiskerRight
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification h)).symm ≪≫
              c_h (HasCompactification.compactification h))
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) ≪≫
          Functor.isoWhiskerLeft
            (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC)
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification e)).symm ≪≫
              c_e (HasCompactification.compactification e)) ≪≫
          (Functor.mapDerivedCategoryCompIso (L h) (L e)).symm ≪≫
          Functor.mapDerivedCategoryNatIso σ)) ∧
        (∀ [Etale h] [Etale e]
          (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale),
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) h).unit.app F).hom.app
              (Opposite.op W) ≫
            ((o h).hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app
              ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((o e).hom.app ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) ≫
            (σ.hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
              (h ≫ e)).unit.app F).hom.app (Opposite.op W) ≫
            ((o (h ≫ e)).hom.app F).hom.app
              (Opposite.op
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale (h ≫ e))).obj W)) ≫
            ((L (h ≫ e)).obj F).obj.map
              ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale h)
                (inferInstance : Etale e)).inv.app W).op)) ∧
      (∀ (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (o f).hom.app F ≫ (ι f).app F =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f F) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X], ∃ i_id : L (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)),
        i_id.hom = ι (𝟙 X) ≫ (lowerStarId (ModuleCat.{u + 1} A) X).hom ∧
        (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
          c_id X (Compactification.ofIsProper (𝟙 X)) ≪≫
          @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
            (F := L (𝟙 X))
            (G := 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (idA X) (by infer_instance) (idL X) (idC X)
            (by infer_instance) (by infer_instance) i_id ≪≫
          Functor.mapDerivedCategoryIdIso _ =
          unboundedEtaleLowerShriekId A X)
```

## New

```lean
theorem quasifiniteCompactSupportExact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (hhq : h.IsQuasiFinite) (ehq : e.IsQuasiFinite) :
    ∃ (L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃ (ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        L f ⟶ lowerStar (ModuleCat.{u + 1} A) f),
      ∃ (o : ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
          (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f],
          etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ L f),
      ∃ (hA : (L h).Additive),
      ∃ (hL : PreservesFiniteLimits (L h)),
      ∃ (hC : PreservesFiniteColimits (L h)),
      ∃ (eA : (L e).Additive),
      ∃ (eL : PreservesFiniteLimits (L e)),
      ∃ (eC : PreservesFiniteColimits (L e)),
      ∃ (heA : (L (h ≫ e)).Additive),
      ∃ (heL : PreservesFiniteLimits (L (h ≫ e))),
      ∃ (heC : PreservesFiniteColimits (L (h ≫ e))),
      ∃ (c_h : ∀ c : Compactification h,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC),
      ∃ (c_e : ∀ c : Compactification e,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L e) eA eL eC),
      ∃ (c_he : ∀ c : Compactification (h ≫ e),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (h ≫ e)) heA heL heC),
      ∃ (idA : ∀ (X : Scheme.{u}) [IsNoetherian X], (L (𝟙 X)).Additive),
      ∃ (idL : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteLimits (L (𝟙 X))),
      ∃ (idC : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteColimits (L (𝟙 X))),
      ∃ (c_id : ∀ (X : Scheme.{u}) [IsNoetherian X] (c : Compactification (𝟙 X)),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (𝟙 X)) (idA X) (idL X) (idC X)),
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (V : Y.Etale),
        Function.Injective (((ι f).app F).hom.app (Opposite.op V)) ∧
        (∀ s : F.obj.obj (Opposite.op
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)),
          (∃ t, (((ι f).app F).hom.app (Opposite.op V)) t = s) ↔
          ∃ T₀ : TopologicalSpace.Closeds
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left,
            (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
              (v₀ : Spec (.of Ω) ⟶
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left),
              v₀ default ∈ T₀ ↔
                (Scheme.pointSmallEtale
                  (v₀ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom)).toPresheafFiber
                    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
                    (Over.homMk v₀) F.obj s ≠ 0) ∧
            IsProper ((Scheme.IdealSheafData.vanishingIdeal T₀).subschemeι ≫
              pullback.fst V.hom f))) ∧
      (∀ c d : Compactification h,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_h d).hom = (c_h c).hom) ∧
      (∀ c d : Compactification e,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_e d).hom = (c_e c).hom) ∧
      (∀ c d : Compactification (h ≫ e),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_he d).hom = (c_he c).hom) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X] (c d : Compactification (𝟙 X)),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_id X d).hom = (c_id X c).hom) ∧
      (∀ (c : Compactification h) (d : Compactification (𝟙 V)),
        (⟨T, h, c⟩ : Σ Y : Scheme.{u}, Σ f : V ⟶ Y, Compactification f) =
          ⟨V, 𝟙 V, d⟩ → HEq (c_h c) (c_id V d)) ∧
      (∀ (c : Compactification e) (d : Compactification (𝟙 T)),
        (⟨B, e, c⟩ : Σ Y : Scheme.{u}, Σ f : T ⟶ Y, Compactification f) =
          ⟨T, 𝟙 T, d⟩ → HEq (c_e c) (c_id T d)) ∧
      (∀ (c : Compactification (h ≫ e)) (d : Compactification (𝟙 V)),
        (⟨B, h ≫ e, c⟩ : Σ Y : Scheme.{u}, Σ f : V ⟶ Y, Compactification f) =
          ⟨V, 𝟙 V, d⟩ → HEq (c_he c) (c_id V d)) ∧
      (∃ σ : L h ⋙ L e ≅ L (h ≫ e),
        (∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          σ.hom.app F ≫ (ι (h ≫ e)).app F =
            (ι e).app ((L h).obj F) ≫
              (lowerStar (ModuleCat.{u + 1} A) e).map ((ι h).app F) ≫
              (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app F) ∧
        ((unboundedEtaleLowerShriekCompIso A h e ≪≫
          (rightDerivedLowerShriekIso A
            (HasCompactification.compactification (h ≫ e))).symm ≪≫
          c_he (HasCompactification.compactification (h ≫ e))) =
          (Functor.isoWhiskerRight
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification h)).symm ≪≫
              c_h (HasCompactification.compactification h))
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) ≪≫
          Functor.isoWhiskerLeft
            (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC)
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification e)).symm ≪≫
              c_e (HasCompactification.compactification e)) ≪≫
          (Functor.mapDerivedCategoryCompIso (L h) (L e)).symm ≪≫
          Functor.mapDerivedCategoryNatIso σ)) ∧
        (∀ [Etale h] [Etale e]
          (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale),
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) h).unit.app F).hom.app
              (Opposite.op W) ≫
            ((o h).hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app
              ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((o e).hom.app ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) ≫
            (σ.hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
              (h ≫ e)).unit.app F).hom.app (Opposite.op W) ≫
            ((o (h ≫ e)).hom.app F).hom.app
              (Opposite.op
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale (h ≫ e))).obj W)) ≫
            ((L (h ≫ e)).obj F).obj.map
              ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale h)
                (inferInstance : Etale e)).inv.app W).op)) ∧
      (∀ (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (o f).hom.app F ≫ (ι f).app F =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f F) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X], ∃ i_id : L (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)),
        i_id.hom = ι (𝟙 X) ≫ (lowerStarId (ModuleCat.{u + 1} A) X).hom ∧
        (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
          c_id X (Compactification.ofIsProper (𝟙 X)) ≪≫
          @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
            (F := L (𝟙 X))
            (G := 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (idA X) (by infer_instance) (idL X) (idC X)
            (by infer_instance) (by infer_instance) i_id ≪≫
          Functor.mapDerivedCategoryIdIso _ =
          unboundedEtaleLowerShriekId A X)
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
--uses quasifiniteCompactSupportExact` lists 18 downstream modules, seven of them direct
importers (EtaleClosedChartExceptionalPreservation, EtaleHorizontalSupportMate,
EtaleSumRightAdjointCoherence, EtaleSupportMapCompatibility, EtaleRhoMonoidalMate,
FiniteSmoothGammaNormalization, FiniteEtaleDualizingNormalization), and reports only the
declaring module as a user of the declaration. No downstream module applies this declaration,
so their statements and proofs require no adaptation. The public imports of the declaring
module are unchanged. No source-library declaration is changed. (Users table completed by the
reviewer from the live library and coord/claims, 2026-10-21.)

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | U1 | Correct the indexed identity antecedents and prove the assembly from four separate normalization lemmas. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | V1 | Direct importer; no Lean use of the changed declaration. Unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Direct importer; no Lean use of the changed declaration. Unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | T8 | Direct importer; no Lean use of the changed declaration. Unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | V2 | Direct importer; no Lean use of the changed declaration. Unchanged. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Direct importer; no Lean use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Direct importer; names the declaration only in a proof-plan docstring (support/sum identification), no Lean use. Unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Direct importer; no Lean use of the changed declaration. Unchanged. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Transitive importer only; no use of the changed declaration. Unchanged. |

The ten current DAG citers are audited individually in the item's `statement_change.citers`.
They use the support/sum comparison, composition, or identity for a fixed indexed map;
they do not require an HEq-only identification of different scheme/morphism indices.
No target's definition is changed, so no target meaning is changed.

## Status

landed 20261021T140922-L-2774891 2026-10-21 (merge of deliver/U1/Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact)

Returned-head repair (`5642e44c844`, reviewer `C-5642e`): this is the delivery
change record, at `coord/changes/quasifinite-compact-support-identity-indices.md`.
If the reviewer supplies an override through `--apply-fixes`, its filename must be
`quasifinite-compact-support-identity-indices.change.md`; the landing tool resolves
change-record overrides by `<stem>.change.md`, not by their repository basename.
The previous `.md` override failed path validation before any landing.
