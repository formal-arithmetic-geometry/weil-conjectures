# AlgebraicGeometry.Etale.exists_qcqsStrictLocalModuleComparison

## Reason

This is the zero-hole retirement at row 2802 of coord/retire-items.tsv, authorized by
coord/changes/retire-sheaf-twins-20261020.md. The adopted twin uses the full affine-neighbourhood
strictLocalizationToBase. The copy uses the small ring-colimit strictHenselizationStructuralMap.
These schemes are canonically isomorphic, but are not definitionally equal. Replacing the import
alone therefore changes the types of all four specialized declarations.

Withdraw the copy and attach its node to the unchanged adopted declarations. Preserve the small
schemes in all consumers. At the three sites which construct comparison isomorphisms, obtain the
adopted comparison and compose it with the global-section isomorphism of the base change of the
canonical small/full ring-colimit isomorphism. The inverse-image composition isomorphism identifies
the coefficient sheaves. The new general unitSectionRestriction_comp theorem transports the germ
equations; pullback extensionality identifies the legs after symmetry.

The other four consumers use only the specialized graph/restriction definitions and the germ
predicate. Express those by the general graph/unit construction for an arbitrary scheme map and
an arbitrary lift of an arbitrary étale object, and expand the predicate as its germ equations.
These expressions are definitionally the former small-model formulas, including proof irrelevance
for the over-category equations. No mathematical statement, underlying scheme, hypothesis or
conclusion changes. This includes empty schemes and the zero coefficient ring.

The new general lemma is fully proved, has no strict-local or geometric-point data, and assumes
neither qcqs nor invertibility. It is not a renamed duplicate of any retired declaration. The
small-model comparison theorem is not recreated under another public name. The seven consumers
are unclaimed; their adaptations are reviewed together with this retirement. No upstream file or
target statement is edited. The unit route stays the same.

## Old

The withdrawn declarations, with definition bodies and theorem signature verbatim:

```lean
noncomputable def qcqsStrictLocalNeighbourhoodSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (pullback f (Scheme.strictHenselizationStructuralMap s))) ⟶
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)).Etale.obj
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.smallStrictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)

noncomputable def qcqsStrictLocalSectionRestriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
    (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F).obj.map
        (qcqsStrictLocalNeighbourhoodSection f s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictHenselizationStructuralMap s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _

def IsQcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F)) : Prop :=
  ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
        qcqsStrictLocalSectionRestriction Λ f s F j

theorem exists_qcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F),
      IsQcqsStrictLocalModuleComparison Λ f s F e.hom
```

The consumer signatures whose notation uses these declarations:

```lean
theorem exists_integralStrictLocalFibreComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Sheaf.Γ (pullback f (strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        qcqsStrictLocalSectionRestriction Λ f s F j ≫ e.hom =
          geometricFibreSectionRestriction Λ sq.toCommSq F
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

```lean
theorem strictLocal_exchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictHenselizationStructuralMap s))
    (hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g')
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F))
    (ha : IsQcqsStrictLocalModuleComparison Λ f s F a) :
    let H := (upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
        (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      eqToHom (by rw [Category.id_comp]) ≫
      a ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
```

```lean
theorem strictLocalFibreRestriction_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
    (ht : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (i : X' ⟶ pullback f (strictHenselizationStructuralMap s))
    (hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g')
    (hi' : i ≫ pullback.snd f (strictHenselizationStructuralMap s) = f' ≫ t)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫ strictLocalFibreRestriction Λ i hi F =
      geometricFibreSectionRestriction Λ sq F
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

```lean
theorem strictLocal_section_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictHenselizationStructuralMap s))
    (hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g')
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) =
      geometricFibreSectionRestriction Λ sq F
        ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)
```

## New

The replacement is the existing adopted module. Its declarations remain verbatim:

```lean
noncomputable def qcqsStrictLocalNeighbourhoodSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (pullback f (Scheme.strictLocalizationToBase s))) ⟶
      (pullback.fst f (Scheme.strictLocalizationToBase s)).Etale.obj
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)

noncomputable def qcqsStrictLocalSectionRestriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
    (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictLocalizationToBase s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F).obj.map
        (qcqsStrictLocalNeighbourhoodSection f s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictLocalizationToBase s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _

def IsQcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F)) : Prop :=
  ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
        qcqsStrictLocalSectionRestriction Λ f s F j

theorem exists_qcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F),
      IsQcqsStrictLocalModuleComparison Λ f s F e.hom
```

The small-model consumer signatures now spell out the same restrictions and germ equations:

```lean
theorem exists_integralStrictLocalFibreComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Sheaf.Γ (pullback f (strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        unitSectionRestriction Λ
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
          (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
            ((equivSmallModel.{u}
              (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
          ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
            Scheme.smallStrictHenselizationBaseChangeMap f s j)
          (by
            change _ ≫ pullback.snd _ f =
              pullback.fst f (Scheme.strictHenselizationStructuralMap s)
            simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
              pullbackSymmetry_hom_comp_snd]) ≫ e.hom =
          geometricFibreSectionRestriction Λ sq.toCommSq F
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

```lean
theorem strictLocal_exchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictHenselizationStructuralMap s))
    (hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g')
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F))
    (ha : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
      unitSectionRestriction Λ
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u}
            (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
        ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j)
        (by
          change _ ≫ pullback.snd _ f =
            pullback.fst f (Scheme.strictHenselizationStructuralMap s)
          simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
            pullbackSymmetry_hom_comp_snd])) :
    let H := (upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
        (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      eqToHom (by rw [Category.id_comp]) ≫
      a ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
```

```lean
theorem strictLocalFibreRestriction_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
    (ht : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (i : X' ⟶ pullback f (strictHenselizationStructuralMap s))
    (hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g')
    (hi' : i ≫ pullback.snd f (strictHenselizationStructuralMap s) = f' ≫ t)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    unitSectionRestriction Λ
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
      (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.smallStrictHenselizationBaseChangeMap f s j)
      (by
        change _ ≫ pullback.snd _ f =
          pullback.fst f (Scheme.strictHenselizationStructuralMap s)
        simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd]) ≫ strictLocalFibreRestriction Λ i hi F =
      geometricFibreSectionRestriction Λ sq F
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

```lean
theorem strictLocal_section_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictHenselizationStructuralMap s))
    (hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g')
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    unitSectionRestriction Λ
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
      (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.smallStrictHenselizationBaseChangeMap f s j)
      (by
        change _ ≫ pullback.snd _ f =
          pullback.fst f (Scheme.strictHenselizationStructuralMap s)
        simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd]) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) =
      geometricFibreSectionRestriction Λ sq F
        ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)
```

The new module Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction defines etaleSectionGraph and
unitSectionRestriction for arbitrary lifts. Its only public theorem is unitSectionRestriction_comp;
its exact statement and complete proof are in that file and its new DAG node.

Six direct imports of the withdrawn module switch to the adopted twin. The general construction
and the existing SmallStrictLocalSectionMaps are public imports only for the four signatures
which mention them; the three comparison-isomorphism consumers use private proof imports.
The public definitions strictLocalFibreRestriction and geometricPointGlobalGerm remain verbatim.
ConstantStrictFibreStalkComparison and QcqsGeometricExchangeFactorization gain theorem-scoped
elaboration options for their longer transport terms, without file-level options or instances.

## Users

The downstream.py --uses scan of the four retired names finds only the withdrawn module and the
seven adapted consumers below. StrictHenselizationModuleFibreFactorization uses the comparison
through StrictLocalExchangeCompatibility, so it is adapted as well as the six current direct
importers. Every affected file was compiled individually against the complete sandbox overlay.
All other importers preserve their interfaces: the four notation-expanded signatures are
definitionally the old small-presentation types. The full downstream.py --names closure follows;
its unchanged rows require no source adaptations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | Q4 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | unclaimed | Withdrawn; node attaches to the official twin. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | unclaimed | Adapted and compiled; same mathematical statement and small-model scheme. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CartesianCoefficientTwists | P2 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoordinateCounitArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteRingSectionDeformation | N1 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteWindow | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralLineDerivedComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralLineRestrictions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralModels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerRefinement | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperOpenTowerComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityConventions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityRankOneLocalData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RankOneClassicalSupportComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RankOneKummerMonomial | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RealWeights | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SectionCentredChartData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SectionLocalComparisonData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SectionLocalDualizingComparisons | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedCupFunctoriality | P5 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedHomPullback | B8 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassChern | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceBaseChangeFirst | V9 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TrfDevissageGeneration | C3 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TwConventions | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WfTateTwist | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | A2 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | C7 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | A4 | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged indirect consumer; all used signatures remain definitionally equivalent. |

## Status

landed 20261022T013415-L-3565988 2026-10-22 (merge of deliver/H2/Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison)
