/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTower

/-! Descent of the affine projection tower equation from comparison images.

Source: etale-origin equivalence and naturality in the final paragraph of the
ordered affine projection calculation.
(blueprint: lem-pur-affine-projection-tower-witness-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity

set_option linter.auxLemma false in
attribute [local instance 100000] AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

private theorem evaluated_eq_of_essSurj
    {C D E B K : Type*} [Category C] [Category D] [Category E] [Category B] [Category K]
    (I : C ⥤ D) (F : D ⥤ E) (G : E ⥤ B) (H : D ⥤ B)
    (Φ : K ⥤ C) [Φ.EssSurj] (a b : I ⋙ F ⋙ G ⟶ I ⋙ H)
    (h : ∀ L, CategoryTheory.evaluateCompositeTransformation I F G H a (Φ.obj L) =
      CategoryTheory.evaluateCompositeTransformation I F G H b (Φ.obj L)) : a = b := by
  ext M
  let e := Φ.objObjPreimageIso M
  apply (cancel_epi ((I ⋙ F ⋙ G).map e.hom)).mp
  rw [a.naturality, b.naturality]
  exact congrArg (fun r => r ≫ (I ⋙ H).map e.hom) (h _)

private theorem transformation_eq_of_essSurj
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Φ : C ⥤ D) [Φ.EssSurj] {F G : D ⥤ E} (a b : F ⟶ G)
    (h : ∀ L, a.app (Φ.obj L) = b.app (Φ.obj L)) : a = b := by
  ext M
  let e := Φ.objObjPreimageIso M
  apply (cancel_epi (F.map e.hom)).mp
  rw [a.naturality, b.naturality, h]

private theorem candidate_comparison_model_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (towerCandidateComparison A c d).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      (compactSupportSiteComparison A c).hom.app L ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d).hom.app L) ≫
        (compactSupportSiteComparison A d).inv.app L := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let model := compactSupportSiteComparison A c ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≪≫
    (compactSupportSiteComparison A d).symm
  have h := Φ.asEquivalence.congrLeft.fullyFaithfulInverse.map_preimage
    (X := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (Y := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) model.hom
  have hh := congr_app h L
  simpa only [towerCandidateComparison, Functor.FullyFaithful.preimageIso_hom,
    Φ, Equivalence.congrLeft, Functor.asEquivalence,
    Functor.whiskeringLeft_obj_map, Functor.whiskeringLeft_obj_obj,
    Functor.comp_obj, Functor.whiskerLeft_app,
    model, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using hh

private theorem candidate_comparison_refl
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    towerCandidateComparison A c c = Iso.refl _ := by
  apply Iso.ext
  apply transformation_eq_of_essSurj
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
  intro L
  rw [candidate_comparison_model_app]
  simp [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl]
  rfl

private theorem candidate_comparison_trans
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e : Compactification f) :
    towerCandidateComparison A c d ≪≫ towerCandidateComparison A d e =
      towerCandidateComparison A c e := by
  apply Iso.ext
  apply transformation_eq_of_essSurj
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
  intro L
  simp only [Iso.trans_hom, NatTrans.comp_app, candidate_comparison_model_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
  rw [← NatTrans.comp_app, ← Iso.trans_hom,
    Etale.rightDerivedLowerShriekOfCompactificationPlusιIso_trans]

private theorem candidate_comparison_cancel_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (O : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    (towerCandidateComparison A c d).hom.app O ≫
        (towerCandidateComparison A d c).hom.app O = 𝟙 _ := by
  have ht := congrArg Iso.hom (candidate_comparison_trans A c d c)
  have hr := congrArg Iso.hom (candidate_comparison_refl A c)
  exact congr_app (ht.trans hr) O

private theorem candidate_comparison_refl_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f)
    (O : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    (towerCandidateComparison A c c).hom.app O = 𝟙 _ := by
  exact congr_app (congrArg Iso.hom (candidate_comparison_refl A c)) O

private def rawTowerTransformation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} {f : X ⟶ T} {g : T ⟶ Y}
    [QuasiCompact f] [QuasiCompact g]
    (b : Compactification g) (e : Compactification (f ≫ b.i)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (b.comp e) := by
  letI : QuasiCompact b.i := b.quasiCompact_openImmersion inferInstance
  exact
    Functor.whiskerLeft (ProperOpenShriek A e.restrict.i)
      (Functor.whiskerRight
        (properOpenMate A (pullback.fst e.g b.i) e.restrict.g e.g b.i
          pullback.condition)
        (lowerStar (ModuleCat.{u + 1} A) b.g).rightDerivedFunctor ≫
      Functor.whiskerLeft (ProperOpenShriek A (pullback.fst e.g b.i))
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g b.g).hom) ≫
    Functor.whiskerRight
      ((properOpenShriekComp A e.restrict.i (pullback.fst e.g b.i)).hom ≫
        (properOpenShriekCongr A e.restrict_i_fst).hom)
      (lowerStar (ModuleCat.{u + 1} A) (e.g ≫ b.g)).rightDerivedFunctor

private theorem rawTowerTransformation_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} {f : X ⟶ T} {g : T ⟶ Y}
    [QuasiCompact f] [QuasiCompact g]
    (b : Compactification g) (e : Compactification (f ≫ b.i)) (M : C A X) :
    (rawTowerTransformation A b e).app M = projectionTowerMap A b e M := by
  simp only [rawTowerTransformation, projectionTowerMap, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]

private def normalizedTowerTransformation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  let c := HasCompactification.compactification f
  let b := HasCompactification.compactification g
  let h := HasCompactification.compactification (f ≫ g)
  let e := h.ofComp b
  Functor.whiskerRight (towerCandidateComparison A c e.restrict).hom
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ≫
    Functor.whiskerLeft
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι
      (rawTowerTransformation A b e) ≫
    (towerCandidateComparison A (b.comp e) h).hom

private def towerEvaluate
    (A : Type (u + 1)) [CommRing A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (t : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (M : C A X) (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj M :=
  CategoryTheory.evaluateCompositeTransformation
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)) t ⟨M, hM⟩

private theorem normalizedTowerTransformation_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (M : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    towerEvaluate A f g (normalizedTowerTransformation A f g) M.obj M.property =
      normalizedProjectionTowerMap A f g M.obj M.property := by
  simp only [towerEvaluate, CategoryTheory.evaluateCompositeTransformation,
    normalizedTowerTransformation,
    normalizedProjectionTowerMap,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj, rawTowerTransformation_app]

private theorem conjugate_cancel_comparisons
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y : C} {z w : D} (a : x ⟶ y) (a' : y ⟶ x)
    (i : F.obj x ⟶ F.obj x) (b : z ⟶ w) (b' : w ⟶ z) (m : F.obj x ⟶ w)
    (ha : a ≫ a' = 𝟙 x) (hi : i = 𝟙 _) (hb : b' ≫ b = 𝟙 w)
    (r : F.obj y ⟶ z) (hr : r = F.map a' ≫ i ≫ m ≫ b') :
    F.map a ≫ r ≫ b = m := by
  rw [hr, hi]
  simp only [Category.assoc, Category.id_comp, hb, Category.comp_id,
    ← F.map_comp_assoc, ha, F.map_id]

-- Keep the specified maps abstract after proving their component formulas.

private theorem normalized_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hraw : ∀ (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
      projectionTowerMap A (HasCompactification.compactification g)
          ((HasCompactification.compactification (f ≫ g)).ofComp
            (HasCompactification.compactification g))
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) =
        towerOriginComposition A f g
          (HasCompactification.compactification g)
          ((HasCompactification.compactification (f ≫ g)).ofComp
            (HasCompactification.compactification g)) L) :
    ∀ (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
      towerEvaluate A f g (normalizedTowerTransformation A f g)
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L).obj
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L).property =
        towerEvaluate A f g (originCompositionAmbient A f g).hom
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L).obj
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L).property := by
  intro L
  let c := HasCompactification.compactification f
  let b := HasCompactification.compactification g
  let h := HasCompactification.compactification (f ≫ g)
  let e := h.ofComp b
  let O := (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b
  refine (normalizedTowerTransformation_app A f g O).trans ?_
  change G.map ((towerCandidateComparison A c e.restrict).hom.app O) ≫
    projectionTowerMap A b e O.obj ≫
    (towerCandidateComparison A (b.comp e) h).hom.app O =
      towerEvaluate A f g (originCompositionAmbient A f g).hom O.obj O.property
  exact conjugate_cancel_comparisons G
    ((towerCandidateComparison A c e.restrict).hom.app O)
    ((towerCandidateComparison A e.restrict c).hom.app O)
    ((towerCandidateComparison A b b).hom.app ((originCompactSupport A f).obj O))
    ((towerCandidateComparison A (b.comp e) h).hom.app O)
    ((towerCandidateComparison A h (b.comp e)).hom.app O)
    (towerEvaluate A f g (originCompositionAmbient A f g).hom O.obj O.property)
    (candidate_comparison_cancel_app A c e.restrict O)
    (candidate_comparison_refl_app A b ((originCompactSupport A f).obj O))
    (candidate_comparison_cancel_app A h (b.comp e) O)
    (projectionTowerMap A b e O.obj) (hraw L)

private theorem originComponent_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (O : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    projectionOriginComponent A f g O.obj O.property =
      towerEvaluate A f g (originCompositionAmbient A f g).hom O.obj O.property := by
  rfl

/-- Descent transports the raw tower equation from comparison images to every
witnessed etale-origin object. The raw equation is an explicit hypothesis so this
statement isolates only the equivalence descent and naturality argument.
Source: lem-pur-compact-support-site-coherence, Step 2 (etale-origin descent).
(blueprint: lem-pur-affine-projection-tower-witness-descent).
-/
theorem projection_tower_witness_descent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : C A X)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hraw : ∀ (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
      projectionTowerMap A (HasCompactification.compactification g)
          ((HasCompactification.compactification (f ≫ g)).ofComp
            (HasCompactification.compactification g))
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) =
        towerOriginComposition A f g
          (HasCompactification.compactification g)
          ((HasCompactification.compactification (f ≫ g)).ofComp
            (HasCompactification.compactification g)) L) :
    normalizedProjectionTowerMap A f g M hM =
      projectionOriginComponent A f g M hM := by
  have hn : normalizedTowerTransformation A f g = (originCompositionAmbient A f g).hom :=
    evaluated_eq_of_essSurj
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
      (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X) _ _
      (normalized_image A f g hraw)
  exact (normalizedTowerTransformation_app A f g ⟨M, hM⟩).symm.trans
    ((congrArg (fun t => towerEvaluate A f g t M hM) hn).trans
      (originComponent_app A f g ⟨M, hM⟩).symm)

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
