/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem tensorShiftGeneric_naturality
    (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (r : ℤ) {M N : _root_.DerivedCategory C} (a : M ⟶ N)
    (T : _root_.DerivedCategory C) :
    (smoothPurityTensorShiftGeneric C r M T).hom ≫
        ((curriedTensor (_root_.DerivedCategory C)).map a).app T =
      (shiftFunctor _ r).map
          (((curriedTensor (_root_.DerivedCategory C)).map a).app (T⟦-r⟧)) ≫
        (smoothPurityTensorShiftGeneric C r N T).hom := by
  let F := curriedTensor (_root_.DerivedCategory C)
  let := _root_.DerivedCategory.commShiftTensorLeft C M
  let := _root_.DerivedCategory.commShiftTensorLeft C N
  have h := NatTrans.shift_app_comm (F.map a) r (T⟦-r⟧)
  have hi : ((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫
      (F.map a).app ((T⟦-r⟧)⟦r⟧) =
      (shiftFunctor _ r).map ((F.map a).app (T⟦-r⟧)) ≫
        ((F.obj N).commShiftIso r).inv.app (T⟦-r⟧) := by
    rw [← cancel_mono (((F.obj N).commShiftIso r).hom.app (T⟦-r⟧))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  change (((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫
      (F.obj M).map ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)) ≫
        (F.map a).app T =
    (shiftFunctor _ r).map ((F.map a).app (T⟦-r⟧)) ≫
      (((F.obj N).commShiftIso r).inv.app (T⟦-r⟧) ≫
        (F.obj N).map ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T))
  have hn := (F.map a).naturality
    ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)
  calc
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg
      (fun z ↦ ((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫ z) hn
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun z ↦ z ≫ (F.obj N).map
        ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)) hi
    _ = _ := Category.assoc _ _ _

/-- The specified tensor-shift comparison commutes with maps in its first factor.
Source: the canonical bifunctor shift structure, as used in step 2 of
`prop-pur-smooth-purity-naturality-cover`. -/
private theorem smoothPurityTensorShift_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (r : ℤ)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N)
    (T : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (smoothPurityTensorShift A X r M T).hom ≫
        ((smoothPurityTensor A X).map a).app T =
      (shiftFunctor _ r).map (((smoothPurityTensor A X).map a).app (T⟦-r⟧)) ≫
        (smoothPurityTensorShift A X r N T).hom := by
  have hM := (existsUnique_smoothPurityTensorShift (ModuleCat.{u + 1} A) X r M T).exists
    |>.choose_spec
  have hN := (existsUnique_smoothPurityTensorShift (ModuleCat.{u + 1} A) X r N T).exists
    |>.choose_spec
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold smoothPurityTensorShift smoothPurityTensorShiftCoefficients
  rw [eM, eN]
  exact tensorShiftGeneric_naturality _ r a T

@[irreducible] private def tensorRightIso {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    {N N' : C} (b : N ≅ N') : T.flip.obj N ≅ T.flip.obj N' :=
  NatIso.ofComponents (fun M ↦ (T.obj M).mapIso b)
    (fun a ↦ ((T.map a).naturality b.hom).symm)

@[irreducible] private def reassociationNatIso (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (d : ℕ) :
    P.compositionTwistShift X d ≅
      (smoothPurityTensor P.Coefficient X).flip.obj (P.diagonalTwist X d) := by
  unfold compositionTwistShift
  exact NatIso.ofComponents (P.smoothPurityReassociation X d)
    (fun a ↦ (smoothPurityTensorShift_naturality P.Coefficient X
      (2 * (d : ℤ)) a (P.diagonalTwist X d)).symm)

@[irreducible] private def derivedPullbackTensorNatIso (A : Type (u + 1)) [CommRing A]
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    (smoothPurityTensor A Y).flip.obj N ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
        (smoothPurityTensor A X).flip.obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N) := by
  letI : IsNoetherianRing A := isNoetherian_of_finite _ _
  letI := ProEtale.upperStarPreservesFlat_moduleCat A
  exact NatIso.ofComponents (fun M ↦ ProEtale.leftDerivedUpperStarTensorIso
    (ModuleCat.{u + 1} A) f M N) (fun a ↦ NatTrans.congr_app
      ((ProEtale.leftDerivedUpperStarTensorNatIso
        (ModuleCat.{u + 1} A) f).hom.naturality a) N)

@[irreducible] private def exactPullbackTensorNatIso (A : Type (u + 1)) [CommRing A]
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    (smoothPurityTensor A Y).flip.obj N ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (smoothPurityTensor A X).flip.obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj N) :=
  let q := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  Functor.isoWhiskerLeft ((smoothPurityTensor A Y).flip.obj N) q.symm ≪≫
    derivedPullbackTensorNatIso A f N ≪≫
    Functor.isoWhiskerRight q ((smoothPurityTensor A X).flip.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)) ≪≫
    Functor.isoWhiskerLeft ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory)
      (tensorRightIso (smoothPurityTensor A X) (q.app N))

private theorem exactPullbackTensorNatIso_app (A : Type (u + 1)) [CommRing A]
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    (exactPullbackTensorNatIso A f N).app M =
      letI : IsNoetherianRing A := isNoetherian_of_finite _ _
      letI := ProEtale.upperStarPreservesFlat_moduleCat A
      compositionPullbackTensor (ModuleCat.{u + 1} A) f M N := by
  let : IsNoetherianRing A := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat A
  have h := (existsUnique_compositionPullbackTensor (ModuleCat.{u + 1} A) f M N).exists
    |>.choose_spec
  have he := eq_of_heq h
  unfold compositionPullbackTensor
  rw [he]
  apply Iso.ext
  simp [exactPullbackTensorNatIso, derivedPullbackTensorNatIso,
    tensorRightIso, compositionTensorMapIso, smoothPurityTensor]

@[irreducible] private def fixedPullbackTensorNatIso (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (smoothPurityTensor P.Coefficient Y).flip.obj N ⋙ P.smoothPurityPullback f ≅
      P.smoothPurityPullback f ⋙ (smoothPurityTensor P.Coefficient X).flip.obj
        ((P.smoothPurityPullback f).obj N) :=
  exactPullbackTensorNatIso P.Coefficient f N

private theorem fixedPullbackTensorNatIso_app (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (fixedPullbackTensorNatIso P f N).app M =
      compositionPullbackTensorFixed P.Ring f M N := by
  have h := (existsUnique_compositionPullbackTensorFixed P.Ring f M N).choose_spec.1
  have he : compositionPullbackTensorFixed P.Ring f M N = _ := eq_of_heq h
  rw [he]
  unfold fixedPullbackTensorNatIso
  exact exactPullbackTensorNatIso_app P.Coefficient f M N

@[irreducible] private def tensorAssociatorNatIsoGeneric {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (N L : C) :
    (curriedTensor C).flip.obj N ⋙ (curriedTensor C).flip.obj L ≅
      (curriedTensor C).flip.obj (((curriedTensor C).obj N).obj L) :=
  NatIso.ofComponents (fun M ↦ α_ M N L)
    (fun a ↦ associator_naturality_left a N L)

private theorem tensorAssociatorNatIsoGeneric_app {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (M N L : C) :
    (tensorAssociatorNatIsoGeneric N L).app M = (α_ M N L) := by
  unfold tensorAssociatorNatIsoGeneric
  rfl

private abbrev tensorAssociatorNatIso (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (N L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (smoothPurityTensor A X).flip.obj N ⋙ (smoothPurityTensor A X).flip.obj L ≅
      (smoothPurityTensor A X).flip.obj (((smoothPurityTensor A X).obj N).obj L) :=
  tensorAssociatorNatIsoGeneric N L

private theorem tensorAssociatorNatIso_app (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (M N L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (tensorAssociatorNatIso A X N L).app M =
      compositionTensorAssociatorFixed A X M N L := by
  have h := (existsUnique_compositionTensorAssociatorFixed A X M N L).choose_spec.1
  have he : compositionTensorAssociatorFixed A X M N L = (α_ M N L) := eq_of_heq h
  rw [he]
  exact tensorAssociatorNatIsoGeneric_app M N L

@[irreducible] private def fixedSourceNatIso (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ) :
    (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse ⋙
        P.smoothPurityPullback (f ≫ g) ⋙ P.compositionTwistShift X (d + e) ≅
      (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse ⋙
        P.smoothPurityPullback g ⋙ P.compositionTwistShift Y e ⋙
        (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor ⋙
        (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙
        P.smoothPurityPullback f ⋙ P.compositionTwistShift X d := by
  let U := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse
  let F := P.smoothPurityPullback f
  let G := P.smoothPurityPullback g
  let H := P.smoothPurityPullback (f ≫ g)
  let T := smoothPurityTensor P.Coefficient X
  let V := smoothPurityTensor P.Coefficient Y
  let i₀ := Functor.isoWhiskerLeft (U ⋙ H) (reassociationNatIso P X (d + e))
  let i₁ := Functor.isoWhiskerLeft U
    (Functor.isoWhiskerRight (compositionFixedPullbackComp P.Ring f g)
      (T.flip.obj (P.diagonalTwist X (d + e))) ≪≫
    Functor.isoWhiskerLeft (G ⋙ F) (tensorRightIso T (P.compositionPowerAdd X d e)))
  let i₂ := Functor.isoWhiskerLeft (U ⋙ G ⋙ F)
    (tensorAssociatorNatIso P.Coefficient X (P.diagonalTwist X e)
      (P.diagonalTwist X d)).symm
  let i₃ := Functor.isoWhiskerLeft (U ⋙ G ⋙ F)
    (Functor.isoWhiskerRight (tensorRightIso T (P.compositionTwistPullback f e).symm)
      (T.flip.obj (P.diagonalTwist X d)))
  let i₄ := Functor.isoWhiskerLeft (U ⋙ G)
    (Functor.isoWhiskerRight (fixedPullbackTensorNatIso P f (P.diagonalTwist Y e)).symm
      (T.flip.obj (P.diagonalTwist X d)))
  let i₅ := Functor.isoWhiskerLeft (U ⋙ G ⋙ V.flip.obj (P.diagonalTwist Y e) ⋙ F)
    (reassociationNatIso P X d).symm
  let i₆ := Functor.isoWhiskerLeft (U ⋙ G)
    (Functor.isoWhiskerRight (reassociationNatIso P Y e).symm (F ⋙ P.compositionTwistShift X d))
  let i₇ := Functor.isoWhiskerLeft (U ⋙ G ⋙ P.compositionTwistShift Y e)
    (Functor.isoWhiskerRight (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso
      (F ⋙ P.compositionTwistShift X d))
  exact i₀ ≪≫ i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆ ≪≫ i₇

set_option maxHeartbeats 2000000 in
-- The eight canonical component types require additional definitional reduction.
private theorem fixedSourceNatIso_normalized (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    P.CompositionSourceNormalized f g d e K ((fixedSourceNatIso P f g d e).app K) := by
  let U := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse
  let F := P.smoothPurityPullback f
  let G := P.smoothPurityPullback g
  let H := P.smoothPurityPullback (f ≫ g)
  let T := smoothPurityTensor P.Coefficient X
  let V := smoothPurityTensor P.Coefficient Y
  let i₀ := Functor.isoWhiskerLeft (U ⋙ H) (reassociationNatIso P X (d + e))
  let i₁ := Functor.isoWhiskerLeft U
    (Functor.isoWhiskerRight (compositionFixedPullbackComp P.Ring f g)
      (T.flip.obj (P.diagonalTwist X (d + e))) ≪≫
    Functor.isoWhiskerLeft (G ⋙ F) (tensorRightIso T (P.compositionPowerAdd X d e)))
  let i₂ := Functor.isoWhiskerLeft (U ⋙ G ⋙ F)
    (tensorAssociatorNatIso P.Coefficient X (P.diagonalTwist X e)
      (P.diagonalTwist X d)).symm
  let i₃ := Functor.isoWhiskerLeft (U ⋙ G ⋙ F)
    (Functor.isoWhiskerRight (tensorRightIso T (P.compositionTwistPullback f e).symm)
      (T.flip.obj (P.diagonalTwist X d)))
  let i₄ := Functor.isoWhiskerLeft (U ⋙ G)
    (Functor.isoWhiskerRight (fixedPullbackTensorNatIso P f (P.diagonalTwist Y e)).symm
      (T.flip.obj (P.diagonalTwist X d)))
  let i₅ := Functor.isoWhiskerLeft (U ⋙ G ⋙ V.flip.obj (P.diagonalTwist Y e) ⋙ F)
    (reassociationNatIso P X d).symm
  let i₆ := Functor.isoWhiskerLeft (U ⋙ G)
    (Functor.isoWhiskerRight (reassociationNatIso P Y e).symm (F ⋙ P.compositionTwistShift X d))
  let i₇ := Functor.isoWhiskerLeft (U ⋙ G ⋙ P.compositionTwistShift Y e)
    (Functor.isoWhiskerRight (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso
      (F ⋙ P.compositionTwistShift X d))
  refine ⟨i₀.app K, i₁.app K, i₂.app K, i₃.app K,
    i₄.app K, i₅.app K, i₆.app K, i₇.app K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold i₀ reassociationNatIso
    exact HEq.rfl
  · unfold i₁ tensorRightIso
    exact HEq.rfl
  · apply heq_of_eq
    exact congrArg Iso.symm (tensorAssociatorNatIso_app P.Coefficient X
      (F.obj (G.obj (U.obj K))) (P.diagonalTwist X e) (P.diagonalTwist X d))
  · apply heq_of_eq
    apply Iso.ext
    simp [i₃, tensorRightIso, compositionTensorMapIso, U, F, G, T,
      smoothPurityPullback]
  · apply heq_of_eq
    apply Iso.ext
    simp [i₄, compositionTensorMapIso, U, G, T,
      ← fixedPullbackTensorNatIso_app, smoothPurityPullback]
  · unfold i₅ reassociationNatIso
    exact HEq.rfl
  · unfold i₆ reassociationNatIso
    exact HEq.rfl
  · exact HEq.rfl
  · unfold fixedSourceNatIso
    exact HEq.rfl

private theorem sourceFixed_eq (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    P.compositionSourceFixed f g d e K = (fixedSourceNatIso P f g d e).app K := by
  exact ((P.existsUnique_compositionSourceFixed f g d e K).choose_spec.2 _
    (fixedSourceNatIso_normalized P f g d e K)).symm

/-- Naturality of the fixed eight-factor source comparison.
Source: thm-pur-composition-coherence.proof.md, Step 2
(blueprint: lem-pur-model-orientation-source-naturality).

Proof: apply naturality of each of the eight normalized factors: shift reassociation,
pullback composition and ordered power splitting, tensor associativity, Tate pullback,
monoidal pullback, the inverse shift reassociation, its pulled-back counterpart, and
the realization unit. Compose their squares in their recorded order. The normalization
uniquely identifies the resulting composites with compositionSourceFixed, and applying
the intrinsic realization functor gives the displayed equality. This works for all
objects and maps, so in particular on finite-Tor constructible objects. -/
theorem model_orientation_source_naturality (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [Y.Over (Spec (.of P.field.k))]
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (K L : Scheme.proEtaleDerivedCategory Z P.Ring) (a : K ⟶ L) :
    ((P.compositionShiftedPullback (f ≫ g) (d + e)).map a) ≫
        (P.compositionSourceIdentification f g d e L).hom =
      (P.compositionSourceIdentification f g d e K).hom ≫
        ((P.compositionShiftedPullback g e) ⋙ (P.compositionShiftedPullback f d)).map a :=
  by
    let R := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor
    have h := (fixedSourceNatIso P f g d e).hom.naturality a
    have hr := congrArg R.map h
    simp only [Functor.map_comp] at hr
    change R.map _ ≫ R.map (P.compositionSourceFixed f g d e L).hom =
      R.map (P.compositionSourceFixed f g d e K).hom ≫ R.map _
    rw [sourceFixed_eq P f g d e K, sourceFixed_eq P f g d e L]
    exact hr


end WeilConjectures.PurityFiniteSetting
