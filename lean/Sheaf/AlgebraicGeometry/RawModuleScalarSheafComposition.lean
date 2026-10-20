module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Scalar forgetting and composition on sheaves

Source: Stacks Project, Tag 03D7; Mathlib canonical Kan-extension and
sheafification comparison unit equations.
(blueprint: lem-sbc-raw-scalar-sheaf-composition).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

-- This unit expansion is the one used in EtaleModuleSetPullbackComparison.
private theorem pullback_unit_hom (A : Type*) [Category.{u + 1} A]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasWeakSheafify (X.smallGrothendieckTopology (Q := @Etale) @Etale) A]
    [∀ P : Y.Etaleᵒᵖ ⥤ A,
      (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) A
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G).hom =
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.lanUnit.app G.obj ≫
      (MorphismProperty.Over.pullback @Etale ⊤ g).op.whiskerLeft
        (toSheafify (D := A) (X.smallGrothendieckTopology (Q := @Etale) @Etale)
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.leftKanExtension G.obj)) := by
  change (sheafToPresheaf Y.smallEtaleTopology A).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) A
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G) = _
  dsimp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.lan, ObjectProperty.ι_obj, Functor.id_obj,
    Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map,
    Iso.refl_hom, NatTrans.id_app, Functor.comp_map,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom, Category.assoc]
  erw [Functor.whiskerLeft_id', Category.comp_id, Category.comp_id]

-- The actual Kan/sheafification comparison, rather than an arbitrary isomorphism,
-- is compatible with the inverse-image adjunction units.
private lemma scalar_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((RawModuleScalarComparison.forget Λ S).obj G) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.pullback Λ f G) =
      (RawModuleScalarComparison.forget Λ S).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let Z := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have : Z.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  have : (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstance
  have : U.IsLeftAdjoint :=
    inferInstanceAs (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  let B := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := B.op
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology U
  have : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      let : PreservesColimitsOfShape (CostructuredArrow L c) U :=
        (Adjunction.ofIsLeftAdjoint U).leftAdjoint_preservesColimits.preservesColimitsOfShape
      let : PreservesColimit (CostructuredArrow.proj L c ⋙ F) U :=
        PreservesColimitsOfShape.preservesColimit
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := U.lanCompIsoOfPreserves L
  let e' := sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let q := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((e.app G.obj).inv) ≫ e'.hom.app (L.lan.obj G.obj)
  have hq : RawModuleScalarComparison.pullback Λ f G = q := by
    simp [RawModuleScalarComparison.pullback, RawModuleScalarComparison.pullbackIso,
      q, e, e', U, B, L]
  rw [hq]
  symm
  apply (sheafToPresheaf _ _).map_injective
  change Functor.whiskerRight
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G).hom U =
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((RawModuleScalarComparison.forget Λ S).obj G)).hom ≫ B.op.whiskerLeft q.hom
  change Functor.whiskerRight
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
      (ModuleCat.{u + 1} Λ) (S.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G).hom U =
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
      AddCommGrpCat.{u + 1} (S.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app
      ((RawModuleScalarComparison.forget Λ S).obj G)).hom ≫ B.op.whiskerLeft q.hom
  rw [pullback_unit_hom (ModuleCat.{u + 1} Λ) f G,
    pullback_unit_hom AddCommGrpCat.{u + 1} f
      ((RawModuleScalarComparison.forget Λ S).obj G)]
  simp only [Functor.whiskerRight_comp, Category.assoc]
  dsimp only [q, ObjectProperty.FullSubcategory.comp_hom]
  rw [← B.op.whiskerLeft_comp]
  have hn := (sheafificationAdjunction X.smallEtaleTopology (AddCommGrpCat.{u + 1})).unit.naturality
    ((e.app G.obj).inv)
  have hs := sheafComposeNatTrans_fac X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _) (L.lan.obj G.obj)
  change (e.app G.obj).inv ≫ toSheafify X.smallEtaleTopology (L.lan.obj G.obj ⋙ U) =
    toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U)) ≫
      ((presheafToSheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})).map (e.app G.obj).inv).hom
    at hn
  change Functor.whiskerRight (L.leftKanExtensionUnit G.obj) U ≫
    L.whiskerLeft (Functor.whiskerRight (toSheafify X.smallEtaleTopology (L.lan.obj G.obj)) U) =
    L.leftKanExtensionUnit (G.obj ⋙ U) ≫ L.whiskerLeft
      (toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U)) ≫
        ((presheafToSheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})).map (e.app G.obj).inv).hom ≫
        (e'.hom.app (L.lan.obj G.obj)).hom)
  change toSheafify X.smallEtaleTopology (L.lan.obj G.obj ⋙ U) ≫
    (e'.hom.app (L.lan.obj G.obj)).hom =
    Functor.whiskerRight (toSheafify X.smallEtaleTopology (L.lan.obj G.obj)) U at hs
  rw [← Category.assoc (toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U))),
    ← hn, Category.assoc, hs]
  rw [B.op.whiskerLeft_comp]
  rw [← Category.assoc]
  change _ = (L.leftKanExtensionUnit (G.obj ⋙ U) ≫
    L.whiskerLeft (U.leftKanExtensionCompIsoOfPreserves G.obj L).inv) ≫ _
  rw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
  rfl


/-- Scalar forgetting commutes with inverse-image composition before deriving.
Source: Stacks Project, Tag 03D7; Mathlib canonical Kan-extension and
sheafification comparison unit equations.
(blueprint: lem-sbc-raw-scalar-sheaf-composition).

Proof: The scalar comparison is constructed from the canonical comparison for
left Kan extension and the canonical comparison for sheafification. Their
unit equations identify its inverse as the mate of the sectionwise scalar
forgetting comparison for direct image. Apply the adjunction hom equivalence
for the composite inverse image to both displayed maps. The defining unit
formula for upperStarComp and the two scalar comparison unit equations make
both transposes the same composite unit followed by sectionwise forgetting.
The hom equivalence is injective, so the displayed maps agree. This uses
only the canonical comparisons, not an arbitrary choice of isomorphism.
Zero sheaves, the zero ring and identity arrows satisfy the same unit equations.
-/
theorem rawModuleScalar_sheaf_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    RawModuleScalarComparison.pullback Λ h' L ≫
        (RawModuleScalarComparison.forget Λ Y').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) =
      (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
          ((RawModuleScalarComparison.forget Λ S).obj L) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map
          (RawModuleScalarComparison.pullback Λ h L) ≫
        RawModuleScalarComparison.pullback Λ a
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)  := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h').homEquiv _ _ |>.injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, scalar_unit Λ h' L]
  change (RawModuleScalarComparison.forget Λ S).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h').unit.app L) ≫
      (RawModuleScalarComparison.forget Λ S).map
        ((lowerStar (ModuleCat.{u + 1} Λ) h').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L)) = _
  rw [← Functor.map_comp,
    upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) a h L h' w.symm]
  rw [Functor.map_comp]
  rw [reassoc_of% (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} a h
    ((RawModuleScalarComparison.forget Λ S).obj L) h' w.symm)]
  rw [reassoc_of% ((lowerStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality
    ((upperStar AddCommGrpCat.{u + 1} a).map
      (RawModuleScalarComparison.pullback Λ h L))).symm]
  erw [((lowerStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality
    (RawModuleScalarComparison.pullback Λ a
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L))).symm]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  have hn := congrArg (lowerStar AddCommGrpCat.{u + 1} h).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.naturality
      (RawModuleScalarComparison.pullback Λ h L))
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn
  rw [reassoc_of% hn.symm]
  rw [← (lowerStar AddCommGrpCat.{u + 1} h).map_comp_assoc
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app
      ((RawModuleScalarComparison.forget Λ Y).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)))
    ((lowerStar AddCommGrpCat.{u + 1} a).map
      (RawModuleScalarComparison.pullback Λ a
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)))]
  rw [scalar_unit Λ a ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)]
  rw [reassoc_of% (scalar_unit Λ h L)]
  rfl

end AlgebraicGeometry.Etale
