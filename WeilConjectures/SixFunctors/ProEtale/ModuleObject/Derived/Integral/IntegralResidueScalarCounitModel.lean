/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorModel
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelMateNormalized
public import WeilConjectures.AlgebraicGeometry.IntegralResidueScalarCounitModel

/-! Scalar-counit normalization for the residue pull square.

The tensor presentation on X has already been normalized to its defining counit.
Only the scalar mate and the ordinary balanced tensor comparison occur below.

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15.
-/

@[expose] public section

universe v u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResidueScalarCounitModel
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

-- Prove the diagram identities with abstract morphisms, before specializing to sheaves.
private theorem counit_inverse_square
    {C : Type*} [Category C] {A B U V W Z : C}
    (p : A ≅ B) (q : W ≅ Z) (a : A ⟶ U) (b : U ⟶ W)
    (c : B ⟶ V) (d : V ⟶ Z)
    (h : a ≫ b ≫ q.hom = p.hom ≫ c ≫ d) :
    p.inv ≫ a ≫ b = c ≫ d ≫ q.inv := by
  calc
    _ = p.inv ≫ (a ≫ b ≫ q.hom) ≫ q.inv := by simp [Category.assoc]
    _ = _ := by rw [h]; simp

private theorem counit_restriction_pasting
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D)
    {A B C' D' E F : C} {U V W Z : D}
    (p : A ⟶ B) (a : B ⟶ C') (b : C' ⟶ D')
    (c : A ⟶ E) (d : E ⟶ F) (ph : F ⟶ D')
    (q : U ⟶ S.obj A) (q' : V ⟶ S.obj E) (f : U ⟶ V)
    (k : S.obj D' ⟶ Z) (k' : S.obj F ⟶ W) (r : W ⟶ Z) (s : V ⟶ W)
    (hm : p ≫ a ≫ b = c ≫ d ≫ ph)
    (ho : S.map ph ≫ k = k' ≫ r)
    (hn : q ≫ S.map c = f ≫ q')
    (hq : q' ≫ S.map d ≫ k' = s) :
    q ≫ S.map p ≫ S.map a ≫ S.map b ≫ k = f ≫ s ≫ r := by
  simp only [← S.map_comp_assoc]
  rw [hm]
  simp only [Functor.map_comp, Category.assoc]
  rw [ho, reassoc_of% hn, reassoc_of% hq]

private theorem counit_tensor_pasting
    {C D H K : Type*} [Category C] [Category D] [Category H] [Category K]
    (F : C ⥤ D) (QY : H ⥤ C) (FH : H ⥤ K) (QX : K ⥤ D)
    (α : QY ⋙ F ⟶ FH ⋙ QX)
    {N N' : C} {U V W : H} {A B Z : K} {L M R R' : D}
    (q : F.obj N ⟶ L) (a : L ⟶ M) (b : M ⟶ R)
    (gX : R ⟶ R') (kX : R' ⟶ QX.obj A) (εX : R ⟶ QX.obj B)
    (gY : N ⟶ N') (kY : N' ⟶ QY.obj U) (εY : N ⟶ QY.obj V)
    (r : FH.obj U ⟶ A) (tX : A ⟶ B) (sX : B ⟶ Z)
    (tY : U ⟶ V) (sY : V ⟶ W) (δ : FH.obj W ⟶ Z)
    (hX : εX = gX ≫ kX ≫ QX.map tX) (hY : εY = gY ≫ kY ≫ QY.map tY)
    (h : q ≫ a ≫ b ≫ gX ≫ kX = F.map (gY ≫ kY) ≫ α.app U ≫ QX.map r)
    (ho : r ≫ tX ≫ sX = FH.map (tY ≫ sY) ≫ δ) :
    q ≫ a ≫ b ≫ εX ≫ QX.map sX =
      F.map εY ≫ α.app V ≫ QX.map (FH.map sY ≫ δ) := by
  rw [hX, hY]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h]
  simp only [← QX.map_comp]
  rw [ho]
  have hn := α.naturality tY
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]

private theorem tensorPresentation_app_port
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (P : HomotopyCategory (Mod C R) (.up ℤ)) :
    (Mod.tensorPresentationDerivedCounit φ).app P =
      (Mod.comap φ).mapDerivedCategory.map ((Mod.extendScalars φ).leftDerivedFunctorCounit.app P) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((Mod.tensorPresentationHomotopyIso φ).hom.app P) := by
  dsimp only [Mod.tensorPresentationDerivedCounit, Mod.extendComapCounit,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  simp only [DerivedCategory.Qh.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
-- Normalize the inverse scalar mate, retaining ordinary restriction factors.
-- Naturality compares the four derived functors with their homotopy models.
private theorem scalar_restriction_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let TX := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X)
    let TY := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) Y)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) Y)
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
    let ph := (NatTrans.mapHomotopyCategory
      (pullIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app P
    let qh := (NatTrans.mapHomotopyCategory
      (comapUpperStarIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app TP
    (residueExchangeRestrictPullIso ℓ E f).hom.app
        ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P)) ≫
      (residueExchangeRestriction ℓ E X).map
        (((residueExchangePullComparisons ℓ E).pull f).inv.app (DerivedCategory.Qh.obj P)) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeReduction ℓ E X).map
          ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P)) ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeReductionCounit ℓ E X).app FP) ≫
      SX.mapDerivedCategoryFactorsh.hom.app ((TX.mapHomotopyCategory (.up ℤ)).obj FP) =
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((residueExchangeRestriction ℓ E Y).map
          ((residueExchangeReductionCounit ℓ E Y).app P) ≫
          SY.mapDerivedCategoryFactorsh.hom.app TP) ≫
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app
        ((SY.mapHomotopyCategory (.up ℤ)).obj TP) ≫
      DerivedCategory.Qh.map (qh ≫ (SX.mapHomotopyCategory (.up ℤ)).map ph) := by
  dsimp only
  let F := (f)^*⟦integralCoeff ℓ E⟧
  let G := (f)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧
  let TX := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X)
  let TY := Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
  let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
  let pH : (TX.mapHomotopyCategory (.up ℤ)).obj FP ≅
      (G.mapHomotopyCategory (.up ℤ)).obj TP :=
    { hom := (NatTrans.mapHomotopyCategory
        (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app P
      inv := (NatTrans.mapHomotopyCategory
        (pullIso (integralReductionMap ℓ E) f).inv (.up ℤ)).app P
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp]
        simp
        rfl
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp]
        simp
        rfl }
  have hm := scalar_mate_counit ℓ E f P
  have hmi : ((residueExchangePullComparisons ℓ E).pull f).inv.app
        (DerivedCategory.Qh.obj P) ≫
      (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P) ≫
      (residueExchangeReductionCounit ℓ E X).app FP =
    (residueExchangeUpperStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((residueExchangeReductionCounit ℓ E Y).app P) ≫
      (residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app TP ≫
      DerivedCategory.Qh.map pH.inv := by
    refine counit_inverse_square
      (((residueExchangePullComparisons ℓ E).pull f).app (DerivedCategory.Qh.obj P))
      (DerivedCategory.Qh.mapIso pH) _ _ _ _ ?_
    unfold residueExchangePullComparisons
    exact hm
  have ho := SX.mapDerivedCategoryFactorsh.hom.naturality pH.inv
  have hq := restrict_pull_fac ℓ E f TP
  have hn := (residueExchangeRestrictPullIso ℓ E f).hom.naturality
    ((residueExchangeReductionCounit ℓ E Y).app P)
  dsimp only [Functor.comp_map] at hn ho
  have h := counit_restriction_pasting (residueExchangeRestriction ℓ E X)
    _ _ _ _ _ _ _ _ _ _ _ _ _ hmi ho hn.symm hq
  simp only [pH, Category.assoc] at h
  simp only [Functor.map_comp, Category.assoc]
  erw [h]

private theorem tensor_counit_app (T : Scheme.{u})
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) :
    let ε : DerivedCategory.Qh ⋙
        (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T) ⟶
      (tensorLeft (residueExchangeOrdinaryCoefficient ℓ E T)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh := by
      unfold residueExchangeReduction integralReduction residueExchangeRestriction
        residueExchangeOrdinaryCoefficient
      exact Mod.tensorPresentationDerivedCounit
        (coefficientMap (integralReductionMap ℓ E) T)
    ε.app P =
    (residueExchangeRestriction ℓ E T).map
      ((residueExchangeReductionCounit ℓ E T).app P) ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory
          (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((Mod.tensorPresentationHomotopyIso
          (coefficientMap (integralReductionMap ℓ E) T)).hom.app P) := by
  dsimp only
  unfold residueExchangeRestriction residueExchangeReductionCounit
    residueExchangeReduction integralReduction
  dsimp only [id]
  exact tensorPresentation_app_port (coefficientMap (integralReductionMap ℓ E) T) P

set_option linter.unusedVariables false in
-- Preserve the original public statement, including its auxiliary SX let.
-- The counit calculation compares several composed concrete module functors.
/-- The scalar pull square, followed by the tensor-presentation counit on X,
computes the ordinary pullback model map. No derived tensor comparison occurs. -/
theorem integralResidue_scalarCounit_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    letI := residueOrdinaryUpperStarMonoidal A f
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let φX := coefficientMap (integralReductionMap ℓ E) X
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
      unfold H B' residueExchangeOrdinaryCoefficient
        residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit φX
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    (residueExchangeRestrictPullIso ℓ E f).hom.app
          ((residueExchangeReduction ℓ E Y).obj M) ≫
      (residueExchangeRestriction ℓ E X).map
        (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
      H.map a ≫
      εX.app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) =
      residueExchangeTensorModelMap ℓ E f P := by
  dsimp only
  have h := scalar_restriction_counit ℓ E f P
  have ho := residueOrdinaryTensorPull_homotopy (integralCoeff ℓ E)
    (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E))
    (integralReductionMap ℓ E) f P
  unfold residueExchangeTensorModelMap Functor.tensorModelMapWith residueExchangeTensorCounit
  dsimp only [id]
  dsimp only at ho
  exact counit_tensor_pasting
    (residueExchangeUpperStar (integralCoeff ℓ E) f) DerivedCategory.Qh
    (((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (tensor_counit_app ℓ E X _) (tensor_counit_app ℓ E Y P) h
    (by simpa only [Category.assoc] using ho)
end AlgebraicGeometry.ProEtale.CondensedRing
