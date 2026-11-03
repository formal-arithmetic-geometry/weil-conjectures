/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.AffineDifferenceTower.AffineDifferenceTowerFactorization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CentredDiagonalSourcePasting
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardSectionPastingBaseChange

/-! # Compatible charts for diagonal deformation pasting

Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1.
(blueprint: lem-pur-composition-compatible-dnc-charts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Functorial action of a bifunctor on two isomorphisms, used before specializing
its coefficient monoidal structures. Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleBifunctorIso {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D ⥤ E) {K K' : C} {L L' : D} (a : K ≅ K') (b : L ≅ L') :
    (F.obj K).obj L ≅ (F.obj K').obj L' :=
  (F.mapIso a).app L ≪≫ (F.obj K').mapIso b

/-- The published tensor bifunctor with the coefficient category fixed once.
Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleTensor (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) :=
  ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B

/-- Derived tensor of two isomorphisms on the actual finite pro-etale category.
Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleTensorIso (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    {K K' L L' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient))}
    (a : K ≅ K') (b : L ≅ L') :=
  compatibleBifunctorIso (P.compatibleTensor B) a b

/-- The canonical comparison-monoidal component checked before fixing its scalar
category. Source: composition proof Steps 5--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleComparisonTensorGeneric (A : Type v₁) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (B : Scheme.{u}) [(ProEtale.comparisonUpperStar A B).PreservesFlat]
    (K L : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)) :
    (ProEtale.comparisonUpperStar A B).mapDerivedCategory.obj
      (((Etale.derivedTensor A B).obj K).obj L) ≅
    ((ProEtale.derivedTensor A B).obj
      ((ProEtale.comparisonUpperStar A B).mapDerivedCategory.obj K)).obj
      ((ProEtale.comparisonUpperStar A B).mapDerivedCategory.obj L) :=
  (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).app L

/-- The published strong monoidal comparison with the scalar category fixed once.
Source: composition proof Steps 5--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleComparisonTensor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (B : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) B).obj K).obj L) ≅
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) B).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj K)).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj L) :=
  letI : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  compatibleComparisonTensorGeneric (ModuleCat.{u + 1} Λ) B K L

private theorem compatibleBifunctorIso_trans {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D ⥤ E) {K K' K'' : C} {L L' L'' : D}
    (a : K ≅ K') (a' : K' ≅ K'') (b : L ≅ L') (b' : L' ≅ L'') :
    compatibleBifunctorIso F a b ≪≫ compatibleBifunctorIso F a' b' =
      compatibleBifunctorIso F (a ≪≫ a') (b ≪≫ b') := by
  ext
  simp only [compatibleBifunctorIso, Functor.mapIso_trans, NatIso.trans_app, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  change (F.map a.hom).app L ≫ (F.obj K').map b.hom ≫
    (F.map a'.hom).app L' ≫ (F.obj K'').map b'.hom =
      (F.map a.hom).app L ≫ (F.map a'.hom).app L ≫
        (F.obj K'').map b.hom ≫ (F.obj K'').map b'.hom
  rw [(F.map a'.hom).naturality_assoc]

private theorem compatibleTensorComparison_naturality
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F : C ⥤ D)
    (m : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj S)
    {K K' L L' : C} (a : K ≅ K') (b : L ≅ L') :
    F.mapIso (compatibleBifunctorIso T a b) ≪≫ (m.app K').app L' =
      (m.app K).app L ≪≫ compatibleBifunctorIso S (F.mapIso a) (F.mapIso b) := by
  apply Iso.ext
  have ha := congr_app (m.hom.naturality a.hom) L
  have hb := (m.hom.app K').naturality b.hom
  dsimp at ha hb
  simp only [compatibleBifunctorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [F.map_comp, Category.assoc, hb, ← Category.assoc, ha]
  simp only [Category.assoc]

private theorem compatibleIso_inverse_square {C : Type u₁} [Category.{v₁} C]
    {W X Y Z : C} (x : W ≅ X) (y : Y ≅ Z) (a : W ≅ Y) (b : X ≅ Z)
    (h : a ≪≫ y = x ≪≫ b) : x.symm ≪≫ a = b ≪≫ y.symm := by
  apply Iso.ext
  change x.inv ≫ a.hom = b.hom ≫ y.inv
  apply (Iso.inv_comp_eq x).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv y).2
  exact congrArg Iso.hom h

/-- The centred neighbourhood data used by the canonical source comparison.
Source: composition proof Step 5; chart-normalization
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
structure CompatibleCentredChart {U V : Scheme.{u}} (r : ℕ) (h : U ⟶ V)
    (x : U ⟶ DiagonalPasting.A r V) where
  neighbourhood : (pullback h h).Opens
  sectionMap : U ⟶ neighbourhood.toScheme
  diagonal : sectionMap ≫ neighbourhood.ι = pullback.diagonal h
  etale : Etale (neighbourhood.ι ≫ chartCoordinateDifferences r h x)
  cartesian : IsPullback sectionMap (𝟙 U)
    (neighbourhood.ι ≫ chartCoordinateDifferences r h x) (DiagonalPasting.zero r U)

/-- The centred source-coordinate comparison; its arrows are computed, not supplied.
Source: composition proof Step 5
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def CompatibleCentredChart.source (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (r : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension r h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (x : U ⟶ DiagonalPasting.A r V) (C : CompatibleCentredChart r h x)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  P.chartSourceCoordinateComparison r h aV x C.neighbourhood C.sectionMap
    C.diagonal C.etale C.cartesian N

open scoped TensorProduct in
section NormalSplitting

variable (P : PurityFiniteSetting.{u})
  {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
  (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
  (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
  (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
  [Etale x] [Etale y]
  (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g)

end NormalSplitting

end WeilConjectures.PurityFiniteSetting
