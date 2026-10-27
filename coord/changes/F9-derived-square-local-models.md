# AlgebraicGeometry.restrictedDirectImageMap and schemeSingleCohomologyComparison

## Reason

The two comparison lemmas must import the existing definitions without importing the theorem they prove. Move the definitions, with their names, signatures and bodies unchanged, to DerivedSquareLocalClassModels. The item publicly imports that module, preserving its public interface. Add two explicit, constructed resolution comparison isomorphisms there. No data are chosen from an unproved existence theorem.

## Old

In lean/Sheaf/AlgebraicGeometry/DerivedSquareLocalClasses.lean:

```lean
/-- Restrict an h-map, keeping the restriction of its global coefficient as target.
Source: Stacks Project, Tag 01FB
(blueprint: lem-weil-pbc-derived-square-local-classes). -/
def restrictedDirectImageMap {Z X : Scheme.{u}} (v : Z ⟶ X)
    {F : X.Modules} {G : Z.Modules} (φ : F ⟶ (pushforward v).obj G) (U : X.Opens) :
    (restrictFunctor U.ι).obj F ⟶
      (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).obj
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) :=
  ((restrictAdjunction U.ι).homEquiv _ _).symm
    (φ ≫ (pushforward v).map ((restrictAdjunction (v ⁻¹ᵁ U).ι).unit.app G) ≫
      (pushforwardComp (v ⁻¹ᵁ U).ι v).hom.app
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) ≫
      ((pushforwardComp (v.resLE U (v ⁻¹ᵁ U) le_rfl) U.ι ≪≫
        pushforwardCongr (v.resLE_comp_ι le_rfl)).inv.app
          ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G)))

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical total/classical comparison, with the total derived-category
universe fixed by the supplied family of scheme module categories.
Source: total/classical right-derived compatibility
(blueprint: lem-weil-pbc-derived-square-local-classes). -/
def schemeSingleCohomologyComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (q : ℕ) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) ≅
      ((pushforward f).rightDerived q).obj F :=
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F q
```

## New

The identical two declarations are in lean/Sheaf/AlgebraicGeometry/DerivedSquareLocalClassModels.lean; the original file has a public import of that module. The new comparison declarations are squareInverseOpenComparison and squareLocalResolutionComparison, built from augmentation and derived-unit isomorphisms and exact homology/evaluation isomorphisms. Both new comparisons are irreducible, with the proved equation
squareInverseOpenComparison_class supplying the class-map API without unfolding
the derived models in consumers. Their signatures and constructions are:

```lean
/-- Inverse-open hypercohomology, evaluated upstairs on the same K-injective model.
Source: Stacks Project, Tag 0D5X
(blueprint: def-weil-pbc-derived-square-local-models). -/
@[irreducible] def squareInverseOpenComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℤ)
    (K : schemeDerivedCategory X) :
    (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom q).obj K ≅
      (TopologicalSpace.Opens.map f.base).op ⋙
        (RingedSpace.localHypercohomologyPresheaf X.toRingedSpace q).obj K :=
  RingedSpace.topEdgeInverseModel f.toLRSHom.toShHom q K ≪≫
    (((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op).mapHomologicalComplexHomologyIso
        (ComplexShape.up ℤ) q).app
          (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (RingedSpace.topEdgeResolution X.toRingedSpace K)) ≪≫
    ((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op).mapIso
        (RingedSpace.topEdgeLocalModel X.toRingedSpace q K).symm

/-- The explicit local section comparison through an augmentation-normalized resolution.
Source: Stacks Project, Tags 01E4 and 0D5X
(blueprint: def-weil-pbc-derived-square-local-models). -/
@[irreducible] def squareLocalResolutionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (q : ℕ) (V : Y.Opens) (I : InjectiveResolution F)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace q).obj
          ((restrictFunctor U.ι).obj F)) ≅
      ((RingedSpace.localHypercohomologyPresheaf Y.toRingedSpace (q : ℤ)).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))).obj (op V) := by
  letI : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  letI := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let Γ := RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)
  letI : Γ.Additive := inferInstanceAs
    (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q
  let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections Y.toRingedSpace
  letI : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let r : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ≅
      DerivedCategory.Q.obj I.cochainComplex :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫ asIso (DerivedCategory.Q.map I.ι')
  let b : (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
      (q : ℤ)).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≅
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).homology
        (q : ℤ) :=
    (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
      (q : ℤ)).mapIso r ≪≫
    (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) (𝟙 I.cochainComplex)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _
  let a := (forget₂ _ AddCommGrpCat.{u}).mapIso
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) q) ≪≫
    (((RingedSpace.globalSectionsComplex R.resolution).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm ≪≫
    H.mapIso (R.sections ≪≫ eqToIso (congrArg (fun W ↦
      ((RingedSpace.openModuleSections X.toRingedSpace W).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) hU)) ≪≫
    (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (q : ℤ)).mapIso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat Γ).symm
  exact a ≪≫
    (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).sc
      (q : ℤ)).mapHomologyIso E ≪≫ E.mapIso b.symm ≪≫
    E.mapIso (RingedSpace.topEdgeLocalLeray f.toLRSHom.toShHom (q : ℤ)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedSquareLocalClasses | F9 | Publicly imports the relocated definitions; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.TopBaseChangePresheaf | unclaimed at local snapshot | Existing names remain publicly visible through the original import; no source adaptation. Compile checked with the relocated definitions. |
| Sheaf.AlgebraicGeometry.TopDegreeBaseChange | unclaimed at local snapshot | Transitive importer; no name or signature changed. |
| Sheaf.AlgebraicGeometry.SquareResolutionLocalClass | new, F9 | Imports the definitions and states the comparison of class maps. |
| Sheaf.AlgebraicGeometry.SquareLocalClassNaturality | new, F9 | Uses the existing normalized class definition, without any changed signature. |
| Sheaf.AlgebraicGeometry.SquareLocalHypercohomology | new, F9 | Imports the definitions and states the pre-sheafification roof calculation. |

## Status

landed 20261025T202016-L-2663496 2026-10-25 (merge of deliver/F9/Sheaf.AlgebraicGeometry.DerivedSquareLocalClasses)
