/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarCompositeModelPasting
import WeilConjectures.SixFunctors.ScalarOpenComposition
import WeilConjectures.SixFunctors.ScalarNormalizedInterchangeSquare

/-! # Scalar extension and compact-support model composition -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate derivedOpenImmersionShriekIso
  compositionInterchangeIsNormalized

private theorem x5_leftAssociateEquality
    {C : Type*} [Category C] {W X Y Z : C}
    {f : W ⟶ Z} {g : W ⟶ X} {h : X ⟶ Y} {i : Y ⟶ Z}
    (he : f = g ≫ h ≫ i) : f = (g ≫ h) ≫ i := by
  simpa only [Category.assoc] using he

private theorem x5_interchangeNaturality
    {B Y Z C : Type*} [Category B] [Category Y] [Category Z] [Category C]
    {P : B ⥤ Y} {I : Y ⥤ C} {L : B ⥤ Z} {R : Z ⥤ C}
    (ι : P ⋙ I ⟶ L ⋙ R) {B₀ B₁ : B} (d : B₀ ⟶ B₁)
    {U V : C} {A : Z} {Y₀ : Y}
    (t : U ⟶ V) (g : V ⟶ R.obj A) (e : A ⟶ L.obj B₀)
    (b : U ⟶ I.obj Y₀) (p : Y₀ ⟶ P.obj B₀)
    (he : t ≫ g ≫ R.map e = b ≫ I.map p ≫ ι.app B₀) :
    t ≫ g ≫ R.map (e ≫ L.map d) =
      (b ≫ I.map (p ≫ P.map d)) ≫ ι.app B₁ := by
  have hn := ι.naturality d
  simp only [Functor.comp_map] at hn
  calc
    _ = (t ≫ g ≫ R.map e) ≫ R.map (L.map d) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (b ≫ I.map p ≫ ι.app B₀) ≫ R.map (L.map d) := by rw [he]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← hn]

private theorem x5_modelPasting
    {B C D B' C' D' : Type*}
    [Category B] [Category C] [Category D]
    [Category B'] [Category C'] [Category D']
    {F : B ⥤ C} {G : C ⥤ D} {H : B ⥤ D}
    {F' : B' ⥤ C'} {G' : C' ⥤ D'} {H' : B' ⥤ D'}
    {T : B ⥤ B'} {V : C ⥤ C'} {W : D ⥤ D'}
    (γF : F ⋙ V ⟶ T ⋙ F') (γG : G ⋙ W ⟶ V ⋙ G')
    (γH : H ⋙ W ⟶ T ⋙ H') (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    {A : C} {A' A'' : C'} {B₀ B₁ : B} {B₀' B₁' : B'}
    (t : A ⟶ F.obj B₀) (o : B₀ ⟶ B₁) (d : T.obj B₁ ⟶ B₁')
    (b₀ : V.obj A ⟶ A'') (b₁ : A'' ⟶ A') (t' : A' ⟶ F'.obj B₀') (o' : B₀' ⟶ B₁')
    (l : T.obj B₀ ⟶ B₀')
    (hc : γH.app B₀ ≫ c'.hom.app (T.obj B₀) =
      W.map (c.hom.app B₀) ≫ γG.app (F.obj B₀) ≫ G'.map (γF.app B₀))
    (ho : T.map o ≫ d = l ≫ o')
    (hi : V.map t ≫ γF.app B₀ ≫ F'.map l = (b₀ ≫ b₁) ≫ t') :
    W.map (G.map t ≫ c.inv.app B₀ ≫ H.map o) ≫ γH.app B₁ ≫ H'.map d =
      (γG.app A ≫ G'.map b₀) ≫ G'.map b₁ ≫
        (G'.map t' ≫ c'.inv.app B₀' ≫ H'.map o') := by
  have hci : W.map (c.inv.app B₀) ≫ γH.app B₀ =
      γG.app (F.obj B₀) ≫ G'.map (γF.app B₀) ≫ c'.inv.app (T.obj B₀) := by
    apply (cancel_mono (c'.hom.app (T.obj B₀))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hc]
    simp only [← W.map_comp_assoc, Iso.inv_hom_id_app, W.map_id, Category.id_comp]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
  have hnH := γH.naturality o
  have hnG := γG.naturality t
  have hnC := c'.inv.naturality l
  simp only [Functor.comp_map] at hnH hnG hnC
  calc
    _ = W.map (G.map t) ≫ (W.map (c.inv.app B₀) ≫ γH.app B₀) ≫
        H'.map (T.map o ≫ d) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (W.map (H.map o)), hnH]
      simp only [Category.assoc]
    _ = γG.app A ≫ G'.map (V.map t ≫ γF.app B₀ ≫ F'.map l) ≫
        c'.inv.app B₀' ≫ H'.map o' := by
      rw [hci, ho]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (W.map (G.map t)), hnG]
      simp only [Category.assoc]
      rw [← Category.assoc (c'.inv.app (T.obj B₀)), ← hnC]
      simp only [Category.assoc]
    _ = _ := by rw [hi]; simp only [Functor.map_comp, Category.assoc]

set_option maxHeartbeats 8000000 in
-- Compare the derived adjunction presentations without expanding their resolutions.
/-- The scalar comparison commutes with the proper/open model compositor, for any map.
Source: latest blueprint, scalar-six compact-support proof, Independence and Composition.
(blueprint: lem-sfb-scalar-composite-pasting).

Proof: expand the model compositor and comparison. Naturality moves the open compositor across the
mate
for the composite proper map. The open-composition law expands the open scalar factor. The
geometric composition law for the proper mate separates the two proper maps. Naturality of the
outer proper mate moves the old interchange inside the outer direct image. Naturality of the
primed proper compositor moves the two open scalar factors inside that same direct image. Apply
the normalized interchange square; naturality of the primed interchange at the inner open scalar
factor now identifies the path with the three factors of the primed model compositor. No
constructibility or scalar invertibility is used. -/
theorem scalarCompositePasting {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X B Y C S : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (p : B ⟶ Y) (i : Y ⟶ C) [IsOpenImmersion i] (q : C ⟶ S) [IsProper p]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (ι : RootCoordinateFace.lower Λ.X p ⋙
        (openImmersionLowerShriek Λ.X i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g)
    (hι : ∀ A, compositionInterchangeIsNormalized Λ.X p i c A (ι.app A))
    (ι' : RootCoordinateFace.lower Λ'.X p ⋙
        (openImmersionLowerShriek Λ'.X i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ'.X c.obj.obj.g)
    (hι' : ∀ A, compositionInterchangeIsNormalized Λ'.X p i c A (ι'.app A))
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a S).map (sfbScalarModelCompositor Λ j p i q c ι K) ≫
      sfbScalarCompactComparison a (j ≫ c.obj.obj.i) (c.obj.obj.g ≫ q) K =
    sfbScalarCompactComparison a i q ((sfbScalarCompactModel Λ j p).obj K) ≫
      (sfbScalarCompactModel Λ' i q).map (sfbScalarCompactComparison a j p K) ≫
      sfbScalarModelCompositor Λ' j p i q c ι' ((scalarSixChange a X).obj K) := by
  classical
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  let A := (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K
  let d : (scalarSixChange a B).obj
      ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) ⟶
      (openImmersionLowerShriek Λ'.X j).mapDerivedCategory.obj
        ((scalarSixChange a X).obj K) :=
    (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom _ _ j _).hom.app K
  let e : (scalarSixChange a c.obj.obj.Z).obj
      ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj A) ⟶
      (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory.obj
        ((scalarSixChange a B).obj A) :=
    (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom _ _ c.obj.obj.i _).hom.app A
  have hopen := scalarOpenComposition a j c.obj.obj.i K
  change (scalarSixChange a c.obj.obj.Z).map
      ((sfbScalarOpenComp Λ j c.obj.obj.i).hom.app K) ≫
      (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom _ _ (j ≫ c.obj.obj.i) _).hom.app K =
    e ≫ (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory.map d ≫
      (sfbScalarOpenComp Λ' j c.obj.obj.i).hom.app
        ((scalarSixChange a X).obj K) at hopen
  have hinter := scalarNormalizedInterchangeSquare a p i c A (ι.app A)
    (ι'.app ((scalarSixChange a B).obj A)) (hι A) (hι' _)
  have hinner := x5_interchangeNaturality ι' d
    ((scalarSixChange a C).map (ι.app A))
    ((scalarDirectImageMate a c.obj.obj.g).app
      ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj A)) e
    ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom _ _ i _).hom.app
        ((RootCoordinateFace.lower Λ.X p).obj A))
    ((scalarDirectImageMate a p).app A) hinter
  have hp := x5_modelPasting
    (scalarDirectImageMate a c.obj.obj.g) (scalarDirectImageMate a q)
    (scalarDirectImageMate a (c.obj.obj.g ≫ q))
    (RootCoordinateFace.lowerComp Λ.X c.obj.obj.g q)
    (RootCoordinateFace.lowerComp Λ'.X c.obj.obj.g q)
    (ι.app A) ((sfbScalarOpenComp Λ j c.obj.obj.i).hom.app K)
    ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
          a.hom.hom a.hom.isMonHom_hom _ _
          (j ≫ c.obj.obj.i) _).hom.app K)
    ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
          a.hom.hom a.hom.isMonHom_hom _ _
          i _).hom.app ((RootCoordinateFace.lower Λ.X p).obj A))
    ((openImmersionLowerShriek Λ'.X i).mapDerivedCategory.map
        ((scalarDirectImageMate a p).app A ≫
          (RootCoordinateFace.lower Λ'.X p).map d))
    (ι'.app ((openImmersionLowerShriek Λ'.X j).mapDerivedCategory.obj
      ((scalarSixChange a X).obj K)))
    ((sfbScalarOpenComp Λ' j c.obj.obj.i).hom.app
      ((scalarSixChange a X).obj K))
    (e ≫ (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory.map d)
    ((scalarDirectImageMateCoherence a c.obj.obj.g q).2.1 _)
    (x5_leftAssociateEquality hopen) hinner
  dsimp only [A, d, scalarSixChange, scalarSixAdjunctionLeft,
    sfbScalarModelCompositor, sfbScalarCompactComparison, sfbScalarCompactModel,
    Functor.comp_map, Functor.comp_obj] at hp ⊢
  convert hp using 1 <;> rfl

end AlgebraicGeometry.ProEtale.CondensedRing
