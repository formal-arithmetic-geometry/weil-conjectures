/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport

/-! # Unary pullback composition in fixed coefficient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local implicit_reducible] realization sixFunctorFiniteRealization
  sixFunctorFinitePullback SemilinearSections.moduleAbelian
  Equivalence.mapDerivedCategory sfIntrinsicPullback sfIntrinsicTransport
  instCategoryDerivedCategory DerivedCategory sfIntrinsicDerivedEquivalence
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

section Coordinates
universe a₀ a₁ a₂ b₀ b₁ b₂ h₀ h₁ h₂ k₀ k₁ k₂
variable {A₀ : Type a₀} {A₁ : Type a₁} {A₂ : Type a₂}
  {B₀ : Type b₀} {B₁ : Type b₁} {B₂ : Type b₂}
  [Category.{h₀} A₀] [Category.{h₁} A₁] [Category.{h₂} A₂]
  [Category.{k₀} B₀] [Category.{k₁} B₁] [Category.{k₂} B₂]

private theorem reassoc_four {V W X Y Z : A₀}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem coefficient_comp_square
    (e₀ : A₀ ≌ B₀) (e₁ : A₁ ≌ B₁) (e₂ : A₂ ≌ B₂)
    (Lg : A₀ ⥤ A₁) (Lf : A₁ ⥤ A₂) (Lc : A₀ ⥤ A₂)
    (k : Lc ≅ Lg ⋙ Lf) (M : A₀) :
    e₂.functor.map (k.hom.app M) ≫
      (e₁.funInvIdAssoc (Lf ⋙ e₂.functor)).inv.app (Lg.obj M) ≫
      (e₁.inverse ⋙ Lf ⋙ e₂.functor).map
        ((e₀.funInvIdAssoc (Lg ⋙ e₁.functor)).inv.app M) =
    (e₀.funInvIdAssoc (Lc ⋙ e₂.functor)).inv.app M ≫
      (Functor.isoWhiskerLeft e₀.inverse (Functor.isoWhiskerRight k e₂.functor) ≪≫
        Functor.isoWhiskerLeft e₀.inverse
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft Lg (e₁.funInvIdAssoc Lf).symm) e₂.functor)).hom.app
              (e₀.functor.obj M) := by
  simp only [Equivalence.funInvIdAssoc_inv_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_map, Functor.comp_obj]
  simp only [← e₂.functor.map_comp, ← Lf.map_comp]
  have hn := e₁.unitIso.hom.naturality (Lg.map (e₀.unit.app M))
  change Lg.map (e₀.unit.app M) ≫ e₁.unit.app _ =
    e₁.unit.app _ ≫ e₁.inverse.map (e₁.functor.map (Lg.map (e₀.unit.app M))) at hn
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [← hn]
  simp only [Lf.map_comp, ← Category.assoc]
  have hk := k.hom.naturality (e₀.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hk
  rw [← hk]

private theorem inverse_coordinate_square (R : A₀ ≌ B₀) (T : A₁ ≌ B₁)
    (F : A₀ ⥤ A₁) (G : B₀ ⥤ B₁)
    (o : G ≅ R.inverse ⋙ F ⋙ T.functor)
    (l : F ⋙ T.functor ≅ R.functor ⋙ G)
    (ho : ∀ N, o.hom.app N ≫ l.hom.app (R.inverse.obj N) =
      G.map (R.counitIso.inv.app N)) (N : B₀) :
    T.functor.map (T.inverse.map (o.hom.app N) ≫
      T.unitIso.inv.app (F.obj (R.inverse.obj N))) ≫ l.hom.app (R.inverse.obj N) =
    T.counitIso.hom.app (G.obj N) ≫ G.map (R.counitIso.inv.app N) := by
  rw [T.functor.map_comp, ← T.counit_app_functor]
  have ht := T.counit.naturality (o.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at ht
  rw [Category.assoc, reassoc_of% ht, ho]

private theorem inverse_coordinate_composition
    (R₀ : A₀ ≌ B₀) (R₁ : A₁ ≌ B₁) (R₂ : A₂ ≌ B₂)
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H : A₀ ⥤ A₂)
    (F' : B₀ ⥤ B₁) (G' : B₁ ⥤ B₂) (H' : B₀ ⥤ B₂)
    (lF : F ⋙ R₁.functor ≅ R₀.functor ⋙ F')
    (lG : G ⋙ R₂.functor ≅ R₁.functor ⋙ G')
    (lH : H ⋙ R₂.functor ≅ R₀.functor ⋙ H')
    (rF : F' ⋙ R₁.inverse ≅ R₀.inverse ⋙ F)
    (rG : G' ⋙ R₂.inverse ≅ R₁.inverse ⋙ G)
    (rH : H' ⋙ R₂.inverse ≅ R₀.inverse ⋙ H)
    (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    (hc : ∀ M, R₂.functor.map (c.hom.app M) ≫ lG.hom.app (F.obj M) ≫
      G'.map (lF.hom.app M) = lH.hom.app M ≫ c'.hom.app (R₀.functor.obj M))
    (hF : ∀ N, R₁.functor.map (rF.hom.app N) ≫ lF.hom.app (R₀.inverse.obj N) =
      R₁.counitIso.hom.app (F'.obj N) ≫ F'.map (R₀.counitIso.inv.app N))
    (hG : ∀ N, R₂.functor.map (rG.hom.app N) ≫ lG.hom.app (R₁.inverse.obj N) =
      R₂.counitIso.hom.app (G'.obj N) ≫ G'.map (R₁.counitIso.inv.app N))
    (hH : ∀ N, R₂.functor.map (rH.hom.app N) ≫ lH.hom.app (R₀.inverse.obj N) =
      R₂.counitIso.hom.app (H'.obj N) ≫ H'.map (R₀.counitIso.inv.app N))
    (N : B₀) :
    R₂.inverse.map (c'.hom.app N) ≫ rG.hom.app (F'.obj N) ≫ G.map (rF.hom.app N) =
      rH.hom.app N ≫ c.hom.app (R₀.inverse.obj N) := by
  apply R₂.functor.map_injective
  apply (cancel_mono (lG.hom.app (F.obj (R₀.inverse.obj N)) ≫
    G'.map (lF.hom.app (R₀.inverse.obj N)))).mp
  simp only [Functor.map_comp, Category.assoc]
  have hn := lG.hom.naturality (rF.hom.app N)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (hG (F'.obj N))]
  rw [← G'.map_comp, hF]
  simp only [Functor.map_comp]
  rw [← G'.map_comp_assoc, Iso.inv_hom_id_app]
  erw [G'.map_id, Category.id_comp]
  have he := R₂.counit.naturality (c'.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at he
  rw [reassoc_of% he]
  have he' := c'.hom.naturality (R₀.counitIso.inv.app N)
  dsimp only [Functor.comp_map] at he'
  dsimp only [Functor.id_obj] at he'
  rw [← he']
  rw [hc (R₀.inverse.obj N), reassoc_of% (hH N)]
  rfl

private def inverseCoordinates (R : A₀ ≌ B₀) (T : A₁ ≌ B₁)
    (F : A₀ ⥤ A₁) (G : B₀ ⥤ B₁) (o : G ≅ R.inverse ⋙ F ⋙ T.functor) :
    G ⋙ T.inverse ≅ R.inverse ⋙ F :=
  Functor.isoWhiskerRight o T.inverse ≪≫
    Functor.isoWhiskerLeft (R.inverse ⋙ F) T.unitIso.symm

private theorem transport_normalization
    (U : B₀ ⥤ A₀) (V : B₁ ⥤ A₁) (W : B₂ ⥤ A₂)
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H : A₀ ⥤ A₂)
    (F' : B₀ ⥤ B₁) (G' : B₁ ⥤ B₂) (H' : B₀ ⥤ B₂)
    (rF : F' ⋙ V ≅ U ⋙ F) (rG : G' ⋙ W ≅ V ⋙ G)
    (rH : H' ⋙ W ≅ U ⋙ H) (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    (hc : ∀ N, W.map (c'.hom.app N) ≫ rG.hom.app (F'.obj N) ≫
      G.map (rF.hom.app N) = rH.hom.app N ≫ c.hom.app (U.obj N))
    (N : B₀) (K : B₁) (L M : B₂)
    (a : L ⟶ M) (sF : M ⟶ G'.obj K) (sG : K ⟶ F'.obj N)
    (sH : L ⟶ H'.obj N)
    (hs : a ≫ sF ≫ G'.map sG = sH ≫ c'.hom.app N) :
    W.map a ≫ W.map sF ≫ rG.hom.app K ≫ G.map (V.map sG ≫ rF.hom.app N) =
      W.map sH ≫ rH.hom.app N ≫ c.hom.app (U.obj N) := by
  have hn := rG.hom.naturality sG
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn]
  rw [← W.map_comp_assoc, ← W.map_comp_assoc, Category.assoc, hs, W.map_comp]
  simp only [Category.assoc]
  rw [hc]

private theorem comparison_composition
    (F Fd : A₀ ⥤ A₁) (G Gd : A₁ ⥤ A₂) (H Hd : A₀ ⥤ A₂)
    (eF : Fd ≅ F) (eG : Gd ≅ G) (eH : Hd ≅ H)
    (c : H ≅ F ⋙ G) (cd : Hd ≅ Fd ⋙ Gd)
    (he : cd.hom = eH.hom ≫ c.hom ≫ Functor.whiskerRight eF.inv G ≫
      Functor.whiskerLeft Fd eG.inv)
    (N : A₀) (K : A₁) (L M : A₂)
    (a : L ⟶ M) (tG : M ⟶ G.obj K) (tF : K ⟶ F.obj N) (tH : L ⟶ H.obj N)
    (ht : a ≫ tG ≫ G.map tF = tH ≫ c.hom.app N) :
    a ≫ tG ≫ eG.inv.app K ≫ Gd.map (tF ≫ eF.inv.app N) =
      tH ≫ eH.inv.app N ≫ cd.hom.app N := by
  have hn := eG.inv.naturality tF
  have hm := eG.inv.naturality (eF.inv.app N)
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn, ← hm]
  have ht' : (a ≫ tG) ≫ G.map tF = tH ≫ c.hom.app N := by
    simpa only [Category.assoc] using ht
  rw [← Category.assoc a tG, ← Category.assoc (a ≫ tG), ht']
  simp only [he, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]

end Coordinates

private def exactPullCoordinates (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfIntrinsicDerivedPullback A f ⋙ (sfIntrinsicDerivedEquivalence X A).inverse ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙ sfFixedDerivedPullback A f :=
  inverseCoordinates (sfIntrinsicDerivedEquivalence Y A) (sfIntrinsicDerivedEquivalence X A)
    (sfFixedDerivedPullback A f) (sfIntrinsicDerivedPullback A f)
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence Y A).inverse
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
          (sfIntrinsicModuleEquivalence X A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))

private theorem exactPullCoordinates_square (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : proEtaleDerivedCategory Y A) :
    let RX := sfIntrinsicDerivedEquivalence X A
    let RY := sfIntrinsicDerivedEquivalence Y A
    let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    let l := Functor.mapDerivedCategorySquareIso
      ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
        (L ⋙ (sfIntrinsicModuleEquivalence X A).functor)).symm
    RX.functor.map ((exactPullCoordinates A f).hom.app N) ≫
      l.hom.app (RY.inverse.obj N) =
    RX.counitIso.hom.app ((sfIntrinsicDerivedPullback A f).obj N) ≫
      (sfIntrinsicDerivedPullback A f).map (RY.counitIso.inv.app N) := by
  exact inverse_coordinate_square
    (sfIntrinsicDerivedEquivalence Y A) (sfIntrinsicDerivedEquivalence X A)
    (sfFixedDerivedPullback A f) (sfIntrinsicDerivedPullback A f) _ _
    (fun N ↦ derived_square_coherence (sfIntrinsicModuleEquivalence Y A)
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
      (sfIntrinsicModuleEquivalence X A).functor N) N

private theorem coefficient_derived_comp_square
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    let EX := sfIntrinsicModuleEquivalence X A
    let EY := sfIntrinsicModuleEquivalence Y A
    let EZ := sfIntrinsicModuleEquivalence Z A
    let Lf := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    let Lg := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g
    let Lc := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g)
    let lf := (EY.funInvIdAssoc (Lf ⋙ EX.functor)).symm
    let lg := (EZ.funInvIdAssoc (Lg ⋙ EY.functor)).symm
    let lc := (EZ.funInvIdAssoc (Lc ⋙ EX.functor)).symm
    EX.functor.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso
            (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) ≪≫
          Functor.mapDerivedCategoryCompIso Lg Lf).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso lf).hom.app (Lg.mapDerivedCategory.obj M) ≫
      (sfIntrinsicPullback A f).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso lg).hom.app M) =
      (Functor.mapDerivedCategorySquareIso lc).hom.app M ≫
        (sfIntrinsicDerivedPullbackComp A f g).hom.app
          (EZ.functor.mapDerivedCategory.obj M) := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let EZ := sfIntrinsicModuleEquivalence Z A
  let Lf := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Lg := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g
  let Lc := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g)
  let lf := (EY.funInvIdAssoc (Lf ⋙ EX.functor)).symm
  let lg := (EZ.funInvIdAssoc (Lg ⋙ EY.functor)).symm
  let lc := (EZ.funInvIdAssoc (Lc ⋙ EX.functor)).symm
  have hq (N) : EX.functor.map
      ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app N) ≫
      lf.hom.app (Lg.obj N) ≫ (sfIntrinsicPullback A f).map (lg.hom.app N) =
        lc.hom.app N ≫ (sfIntrinsicPullbackComp A f g).hom.app (EZ.functor.obj N) := by
    exact coefficient_comp_square EZ EY EX Lg Lf Lc
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) N
  have h := Functor.mapDerivedCategorySquareIso_comp Lg Lf Lc
    (sfIntrinsicPullback A g) (sfIntrinsicPullback A f) (sfIntrinsicPullback A (f ≫ g))
    EZ.functor EY.functor EX.functor lg lf lc
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g)
    (sfIntrinsicPullbackComp A f g) hq
  have hh := congrArg (fun t ↦ t.hom.app M) h
  dsimp only [EX, EY, EZ, Lf, Lg, Lc, lf, lg, lc,
    sfIntrinsicDerivedPullbackComp, sfIntrinsicPullback, sfIntrinsicTransport] at hh ⊢
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using hh

private theorem exactPullCoordinates_comp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : proEtaleDerivedCategory Z A) :
    (sfIntrinsicDerivedEquivalence X A).inverse.map
        ((sfIntrinsicDerivedPullbackComp A f g).hom.app N) ≫
      (exactPullCoordinates A f).hom.app ((sfIntrinsicDerivedPullback A g).obj N) ≫
      (sfFixedDerivedPullback A f).map ((exactPullCoordinates A g).hom.app N) =
    (exactPullCoordinates A (f ≫ g)).hom.app N ≫
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((sfIntrinsicDerivedEquivalence Z A).inverse.obj N) := by
  exact inverse_coordinate_composition
    (sfIntrinsicDerivedEquivalence Z A) (sfIntrinsicDerivedEquivalence Y A)
    (sfIntrinsicDerivedEquivalence X A)
    (sfFixedDerivedPullback A g) (sfFixedDerivedPullback A f)
    (sfFixedDerivedPullback A (f ≫ g))
    (sfIntrinsicDerivedPullback A g) (sfIntrinsicDerivedPullback A f)
    (sfIntrinsicDerivedPullback A (f ≫ g)) _ _ _
    (exactPullCoordinates A g) (exactPullCoordinates A f) (exactPullCoordinates A (f ≫ g))
    _ (sfIntrinsicDerivedPullbackComp A f g)
    (coefficient_derived_comp_square A f g)
    (exactPullCoordinates_square A g) (exactPullCoordinates_square A f)
    (exactPullCoordinates_square A (f ≫ g)) N

set_option maxHeartbeats 800000 in
-- Comparing the intrinsic and fixed derived coordinates requires a larger elaboration budget.
/-- The operation pullback compositor realizes the canonical fixed-scalar compositor.
This is a unary normalization: no tensor, compact support or projection occurs.

Source: finitePullCompositionNormalization of def-sf-operation-stages and the
coefficient-unit cancellation in the composition clause of
fix-prop-projection-formula.proof.md
(blueprint: lem-sf-finite-pullback-composition-realization).

Proof: apply inverse coefficient realization to finitePullCompositionNormalization.
Expand pullRealization using the two mapDerivedCategoryCompIso comparisons. Their
associativity and naturality identify the intrinsic compositor with the localization
of upperStarComp, with the inverse coefficient unit inserted between the two
pullbacks. Naturality of that unit moves the inner pullback comparison past it;
the adjacent unit and inverse cancel. Finally expand leftDerivedUpperStarComp:
its exact-to-left-derived comparisons cancel the fixedPullComparison factors
in fixedPullRealization. The pComp field of ordinary is this canonical compositor.
This leaves precisely the equation below. The argument
uses exact inverse image and works for every bounded constructible input, including
zero objects, empty schemes, identity morphisms and exponent one. -/
theorem fixedPullRealization_composition
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : sixFunctorFiniteCategory D C E n hn Z) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)) ≫
      (fixedPullRealization S f ((S.finite.pull g).obj N) ≪≫
        (fixedDerivedPull (C := C) (E := E) (n := n) f).mapIso
          (fixedPullRealization S g N)).hom =
    (fixedPullRealization S (f ≫ g) N).hom ≫
      ((ordinary D A).pComp f g).hom.app
        (RZ.inverse.obj N.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  dsimp only
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let a := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.map
    ((S.finite.pullComposition f g).hom.app N)
  let c := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.hom.left g.hom.left) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have ht := transport_normalization RZ.inverse RY.inverse RX.inverse
    (sfFixedDerivedPullback A g.hom.left) (sfFixedDerivedPullback A f.hom.left)
    (sfFixedDerivedPullback A (f ≫ g).hom.left)
    (sfIntrinsicDerivedPullback A g.hom.left) (sfIntrinsicDerivedPullback A f.hom.left)
    (sfIntrinsicDerivedPullback A (f ≫ g).hom.left)
    (exactPullCoordinates A g.hom.left) (exactPullCoordinates A f.hom.left)
    (exactPullCoordinates A (f ≫ g).hom.left) c
    (sfIntrinsicDerivedPullbackComp A f.hom.left g.hom.left)
    (exactPullCoordinates_comp A f.hom.left g.hom.left)
    N.obj ((S.finite.pull g).obj N).obj
    ((S.finite.pull (f ≫ g)).obj N).obj
    ((S.finite.pull f).obj ((S.finite.pull g).obj N)).obj a
    ((S.finitePullback f).hom.app ((S.finite.pull g).obj N))
    ((S.finitePullback g).hom.app N) ((S.finitePullback (f ≫ g)).hom.app N)
    (S.finitePullCompositionNormalization f g N)
  have he : (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A))
      f.hom.left g.hom.left).hom =
      (fixedPullComparison (C := C) (E := E) (n := n) (f ≫ g)).hom ≫ c.hom ≫
        Functor.whiskerRight (fixedPullComparison (C := C) (E := E) (n := n) g).inv
          (sfFixedDerivedPullback A f.hom.left) ≫
        Functor.whiskerLeft (fixedDerivedPull (C := C) (E := E) (n := n) g)
          (fixedPullComparison (C := C) (E := E) (n := n) f).inv := by
    delta fixedPullComparison leftDerivedUpperStarComp
    simp only [c,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Category.assoc]
    simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_assoc]
    rfl
  have h := comparison_composition
    (sfFixedDerivedPullback A g.hom.left) (fixedDerivedPull (C := C) (E := E) (n := n) g)
    (sfFixedDerivedPullback A f.hom.left) (fixedDerivedPull (C := C) (E := E) (n := n) f)
    (sfFixedDerivedPullback A (f ≫ g).hom.left)
    (fixedDerivedPull (C := C) (E := E) (n := n) (f ≫ g))
    (fixedPullComparison g) (fixedPullComparison f) (fixedPullComparison (f ≫ g))
    c (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A))
      f.hom.left g.hom.left) he
    (RZ.inverse.obj N.obj) (RY.inverse.obj ((S.finite.pull g).obj N).obj) _ _
    (RX.inverse.map a)
    (RX.inverse.map ((S.finitePullback f).hom.app ((S.finite.pull g).obj N)) ≫
      (exactPullCoordinates A f.hom.left).hom.app ((S.finite.pull g).obj N).obj)
    (RY.inverse.map ((S.finitePullback g).hom.app N) ≫
      (exactPullCoordinates A g.hom.left).hom.app N.obj)
    (RX.inverse.map ((S.finitePullback (f ≫ g)).hom.app N) ≫
      (exactPullCoordinates A (f ≫ g).hom.left).hom.app N.obj)
    (by simpa only [Category.assoc] using ht)
  change RX.inverse.map a ≫
    (fixedPullRealization S f ((S.finite.pull g).obj N)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (fixedPullRealization S g N).hom =
    (fixedPullRealization S (f ≫ g) N).hom ≫ _
  have hr {U V : SixFunctorSpace D} (j : U ⟶ V)
      (L : sixFunctorFiniteCategory D C E n hn V) :
      (fixedPullRealization S j L).hom =
        (realization (C := C) (E := E) (n := n) (hn := hn) U).inverse.map
          ((S.finitePullback j).hom.app L) ≫
        (exactPullCoordinates A j.hom.left).hom.app L.obj ≫
        (fixedPullComparison (C := C) (E := E) (n := n) j).inv.app
          ((realization (C := C) (E := E) (n := n) (hn := hn) V).inverse.obj L.obj) := by
    dsimp only [fixedPullRealization, pullRealization, exactPullCoordinates,
      inverseCoordinates, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      Functor.mapIso_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    dsimp only [Iso.trans, Iso.app, Functor.category, NatTrans.vcomp] at *
    erw [Functor.map_comp]
    simp only [Category.assoc]
    rfl
  rw [hr f, hr g, hr (f ≫ g)]
  dsimp only [RX, RY, RZ, A, ordinary] at h ⊢
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  exact h.trans (reassoc_four _ _ _ _)

end WeilConjectures.CompactSupportFiniteProjection
