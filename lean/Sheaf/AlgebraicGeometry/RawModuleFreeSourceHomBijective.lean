/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups R1 and B2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Underived free-source scalar comparison

Source: Stacks Project, Tags 03FD, 03D3 and 03D7.
(blueprint: lem-sbc-raw-module-free-source-hom-bijective).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

-- Sheafification, the free abelian group adjunction, and Yoneda identify Hom with sections.
private noncomputable def abelianSections (S : Scheme.{u}) (U : S.Etale)
    (N : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (RawModuleScalarComparison.freeAbelian S U ⟶ N) ≃ N.obj.obj (op U) :=
  ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) N).trans
      ((((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv)

private lemma abelianSections_comp (S : Scheme.{u}) (U : S.Etale)
    {N N' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : RawModuleScalarComparison.freeAbelian S U ⟶ N) (b : N ⟶ N') :
    abelianSections S U N' (a ≫ b) = b.hom.app (op U) (abelianSections S U N a) := by
  dsimp only [abelianSections, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  change uliftYonedaEquiv
    (((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _
      (((sheafificationAdjunction _ _).homEquiv _ _ a) ≫ b.hom)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma freeMap_sections (Λ : Type (u + 1)) [CommRing Λ]
    (S : Scheme.{u}) (U : S.Etale)
    (N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (g : (freeSheaf Λ S).obj U ⟶ N) :
    abelianSections S U ((RawModuleScalarComparison.forget Λ S).obj N)
      (RawModuleScalarComparison.freeMap Λ S U ≫
        (RawModuleScalarComparison.forget Λ S).map g) = freeSheafHomEquiv Λ U N g := by
  rw [abelianSections_comp]
  have hg := freeSheafHomEquiv_comp Λ U (𝟙 ((freeSheaf Λ S).obj U)) g
  change (g.hom.app (op U)).hom
    (abelianSections S U ((RawModuleScalarComparison.forget Λ S).obj
      ((freeSheaf Λ S).obj U))
      ((abelianSections S U ((RawModuleScalarComparison.forget Λ S).obj
        ((freeSheaf Λ S).obj U))).symm
      (freeSheafHomEquiv Λ U ((freeSheaf Λ S).obj U) (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa using hg.symm

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

/-- The explicit generator comparison is bijective on underived Hom.
Source: Stacks Project, Tag 03FD, equality of section complexes; Tags 03D3 and 03D7.
(blueprint: lem-sbc-raw-module-free-source-hom-bijective).

Proof: Apply the inverse-image/direct-image adjunction in modules and in
abelian sheaves. Then apply sheafification adjunction, the free-module/free-group
adjunction and Yoneda. Both Hom groups become the same section group of f_*M
at U. The two units commute with the Kan-extension/sheafification comparison
pullbackIso. The definition of freeMap sends the identity generator to the
identity generator, so f ↦ a ≫ forget(f) becomes the identity on that section
group. It is therefore bijective. This works for every M, independently of
injectivity, in degree zero, over the zero ring, and on empty schemes. -/
theorem rawModuleFreeSourceHom_bijective
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun g :
        (upperStar (ModuleCat.{u + 1} Λ) f).obj ((freeSheaf Λ S).obj U) ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
          (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f ((freeSheaf Λ S).obj U)) ≫
          (RawModuleScalarComparison.forget Λ X).map g) := by
  let L := (freeSheaf Λ S).obj U
  -- Both equivalences have the same section group as codomain.
  let em := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv L M).trans
    (freeSheafHomEquiv Λ U ((lowerStar (ModuleCat.{u + 1} Λ) f).obj M))
  let ea := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
    (RawModuleScalarComparison.freeAbelian S U)
    ((RawModuleScalarComparison.forget Λ X).obj M)).trans
      (abelianSections S U ((lowerStar AddCommGrpCat.{u + 1} f).obj
        ((RawModuleScalarComparison.forget Λ X).obj M)))
  let e := em.trans ea.symm
  have he : (fun g : (upperStar (ModuleCat.{u + 1} Λ) f).obj L ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f L) ≫
        (RawModuleScalarComparison.forget Λ X).map g) = e := by
    funext g
    apply ea.injective
    change ea _ = ea (ea.symm (em g))
    rw [Equiv.apply_symm_apply]
    dsimp only [ea, em, Equiv.trans_apply]
    rw [Category.assoc, Adjunction.homEquiv_naturality_left]
    rw [Adjunction.homEquiv_apply, Functor.map_comp]
    rw [← Category.assoc
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((RawModuleScalarComparison.forget Λ S).obj L))
      ((lowerStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.pullback Λ f L))]
    rw [scalar_unit Λ f L]
    change abelianSections S U ((RawModuleScalarComparison.forget Λ S).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj M))
      (RawModuleScalarComparison.freeMap Λ S U ≫
        (RawModuleScalarComparison.forget Λ S).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv L M g)) = _
    exact freeMap_sections Λ S U _ _
  change Function.Bijective (fun g : (upperStar (ModuleCat.{u + 1} Λ) f).obj L ⟶ M ↦ _)
  rw [he]
  exact e.bijective

end AlgebraicGeometry.Etale
