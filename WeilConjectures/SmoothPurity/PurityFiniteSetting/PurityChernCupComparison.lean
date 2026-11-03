/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitNaturality

/-! # Exact comparison of the specified ordered cup step
Source: Stacks Tag 0FI5, equation-chern-classes.
(blueprint: lem-pur-chern-cup-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem exact_tensor_comparison
    {B : Type v} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [BraidedCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {D : Type w} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [BraidedCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (K M : DerivedCategory B) :
    let i := Functor.isoWhiskerLeft ((curriedTensor (DerivedCategory B)).obj K)
        F.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (asIso F.leftDerivedTensorComparison).app K ≪≫
      Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory
        ((curriedTensor (DerivedCategory D)).obj (F.leftDerivedFunctor.obj K)) ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        ((curriedTensor (DerivedCategory D)).mapIso
          (F.leftDerivedFunctorIsoMapDerivedCategory.app K))
    i.hom.app M = (F.mapDerivedCategoryTensorComparison.app K).app M := by
  dsimp only
  rw [Functor.mapDerivedCategoryTensorComparison_app_app]
  simp -implicitDefEqProofs only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, asIso_hom, Functor.mapIso_hom, tensorHom_def']
  rfl

private theorem tensor_comparison_hom
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) [(ProEtale.comparisonUpperStar B T).PreservesFlat]
    (K M : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K).hom.app M =
      ((ProEtale.comparisonUpperStar B T).mapDerivedCategoryTensorComparison.app K).app M := by
  unfold ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
  have h := exact_tensor_comparison (ProEtale.comparisonUpperStar B T) K M
  simp -implicitDefEqProofs only [Etale.derivedTensor, ProEtale.derivedTensor] at h ⊢
  with_unfolding_all exact h

private theorem cup_comparison
    {B D : Type*} [Category B] [Category D]
    (F : B ⥤ D) (S : B ⥤ B ⥤ B) (R : D ⥤ D ⥤ D)
    (d : (Functor.postcompose₂.obj F).obj S ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj R)
    (U K L : B) (delta : U ⟶ (S.obj U).obj U) (a : U ⟶ K) (b : U ⟶ L)
    (eUU : F.obj ((S.obj U).obj U) ≅ (R.obj (F.obj U)).obj (F.obj U))
    (eKL : F.obj ((S.obj K).obj L) ≅ (R.obj (F.obj K)).obj (F.obj L))
    (hUU : eUU.hom = (d.app U).app U) (hKL : eKL.hom = (d.app K).app L) :
    F.map delta ≫ eUU.hom ≫ (R.map (F.map a)).app (F.obj U) ≫
        (R.obj (F.obj K)).map (F.map b) ≫ eKL.inv =
      F.map (delta ≫ (S.map a).app U ≫ (S.obj K).map b) := by
  have h₁ := NatTrans.congr_app (d.naturality a) U
  have h₂ := (d.app K).naturality b
  change F.map ((S.map a).app U) ≫ (d.app K).app U =
    (d.app U).app U ≫ (R.map (F.map a)).app (F.obj U) at h₁
  change F.map ((S.obj K).map b) ≫ (d.app K).app L =
    (d.app K).app U ≫ (R.obj (F.obj K)).map (F.map b) at h₂
  rw [hUU]
  simp only [Functor.map_comp]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, ← hKL, Iso.hom_inv_id, Category.comp_id]

private theorem geometric_cup_comparison
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) [(ProEtale.comparisonUpperStar B T).PreservesFlat]
    (U K L : DerivedCategory (Sheaf T.smallEtaleTopology B))
    (delta : U ⟶ ((Etale.derivedTensor B T).obj U).obj U)
    (a : U ⟶ K) (b : U ⟶ L) :
    let F := (ProEtale.comparisonUpperStar B T).mapDerivedCategory
    F.map delta ≫
        (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B U).hom.app U ≫
        ((ProEtale.derivedTensor B T).map (F.map a)).app (F.obj U) ≫
        ((ProEtale.derivedTensor B T).obj (F.obj K)).map (F.map b) ≫
        (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K).inv.app L =
      F.map (delta ≫ ((Etale.derivedTensor B T).map a).app U ≫
        ((Etale.derivedTensor B T).obj K).map b) := by
  exact cup_comparison _ _ _
    (ProEtale.comparisonUpperStar B T).mapDerivedCategoryTensorComparison U K L delta a b
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B U).app U)
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K).app L)
    (tensor_comparison_hom B T U U) (tensor_comparison_hom B T K L)

/-- The exact site comparison preserves the actual ordered hyperplane step.
Source: Stacks Tag 0FI5, full-support cup products in equation-chern-classes.
Proof: identify the recorded tensor comparison with the natural tensor comparison
of the exact derived functor over a general coefficient category. Naturality in
its two variables moves the class and Kummer arrow across it. Cancel the remaining
comparison with its inverse and specialize to finite module coefficients.
(blueprint: lem-pur-chern-cup-comparison). -/
theorem ordinaryFiniteHyperplaneStep_comparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ)
    (α : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T i) :
    P.ordinaryFiniteHyperplaneStep T h i
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map α) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
      (projectiveBundleUnitDiagonal P.Coefficient T ≫
        ((Etale.ordinaryFiniteTensor P.Coefficient T).map α).app
          (Etale.ordinaryFiniteUnit P.Coefficient T) ≫
        ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
          (P.diagonalTwistEtale T i)).map h) := by
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite P.Coefficient P.Coefficient
  let : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  exact geometric_cup_comparison (ModuleCat.{u + 1} P.Coefficient) T
    (Etale.ordinaryFiniteUnit P.Coefficient T) (P.diagonalTwistEtale T i)
    ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (projectiveBundleUnitDiagonal P.Coefficient T) α h

/-- The ordered etale product of a specified class with j hyperplane classes.
This is a construction in the same positive Tate powers as the published
pro-etale product; no transport or primitive root is chosen.
Source: Stacks Tag 0FI5, the product in equation-chern-classes.
(blueprint: lem-pur-chern-cup-comparison). -/
def ordinaryFiniteEtaleHyperplaneProduct (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T i) :
    (j : ℕ) → Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T (i + j)
  | 0 => α
  | j + 1 => projectiveBundleUnitDiagonal P.Coefficient T ≫
      ((Etale.ordinaryFiniteTensor P.Coefficient T).map
        (P.ordinaryFiniteEtaleHyperplaneProduct T h i α j)).app
          (Etale.ordinaryFiniteUnit P.Coefficient T) ≫
      ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
        (P.diagonalTwistEtale T (i + j))).map h

/-- Exact comparison preserves every ordered product, including its initial class.
Source: Stacks Tag 0FI5, ordered cup products in the projective relation.
Proof: at exponent zero both expressions are the compared initial class.
At a successor apply the induction hypothesis and the proved cup-step comparison.
The two outputs use exactly the same index i+j, so no degree transport is suppressed.
(blueprint: lem-pur-chern-cup-comparison). -/
theorem ordinaryFiniteHyperplaneProduct_comparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T i)
    (j : ℕ) :
    P.ordinaryFiniteHyperplaneProduct T h i
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map α) j =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (P.ordinaryFiniteEtaleHyperplaneProduct T h i α j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    dsimp only [ordinaryFiniteHyperplaneProduct, ordinaryFiniteEtaleHyperplaneProduct]
    rw [ih]
    exact P.ordinaryFiniteHyperplaneStep_comparison T h (i + j) _

/-- An ordered etale cup step is postcomposition by one fixed coefficient arrow.
Source: Stacks Tag 0FI5, multiplication by the hyperplane class.
Proof: naturality of the inverse coefficient right unitor moves the arbitrary
input arrow past the unit diagonal, leaving its postcomposition with right cup
multiplication. The existing single-unit naturality theorem retains exactly
the recorded coefficient-unit normalization.
(blueprint: lem-pur-chern-cup-comparison). -/
theorem ordinaryFiniteEtaleHyperplaneStep_postcompose (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T i) :
    projectiveBundleUnitDiagonal P.Coefficient T ≫
        ((Etale.ordinaryFiniteTensor P.Coefficient T).map α).app
          (Etale.ordinaryFiniteUnit P.Coefficient T) ≫
        ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
          (P.diagonalTwistEtale T i)).map h =
      α ≫ (Etale.derivedTensorSingleUnitIso (P.diagonalTwistEtale T i)).inv ≫
        ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
          (P.diagonalTwistEtale T i)).map h := by
  have hn := Etale.ordinaryFiniteSingleUnit_naturality P.Coefficient T α
  simpa only [projectiveBundleUnitDiagonal, Category.assoc] using
    (congrArg (fun z ↦ z ≫
      ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
        (P.diagonalTwistEtale T i)).map h) hn).symm

/-- Every ordinary pro-etale cup step is postcomposition with the compared right
multiplication map; the input class need not come with a chosen etale presentation.
Source: Stacks Tags 099V and 0FI5, comparison and cup multiplication.
Proof: lift the input uniquely by finite site comparison, apply the proved step
comparison and etale postcomposition identity, then combine mapped compositions.
(blueprint: lem-pur-chern-cup-comparison). -/
theorem ordinaryFiniteHyperplaneStep_postcompose (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteHyperplaneStep T h i α =
      α ≫ (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          ((Etale.derivedTensorSingleUnitIso (P.diagonalTwistEtale T i)).inv ≫
            ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
              (P.diagonalTwistEtale T i)).map h) := by
  obtain ⟨β, rfl⟩ := (P.ordinaryFiniteCohomologyComparison_bijective a i).2 α
  rw [ordinaryFiniteHyperplaneStep_comparison,
    ordinaryFiniteEtaleHyperplaneStep_postcompose, Functor.map_comp]

/-- The actual etale coefficient morphism for right multiplication by h^j.
It starts with the identity and successively composes with the recorded inverse
right unit and tensoring by h. Source: Stacks Tag 0FI5, multiplication by h^j.
(blueprint: lem-pur-chern-cup-comparison). -/
def ordinaryFiniteEtaleHyperplaneProductMap (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧) (i : ℕ) :
    (j : ℕ) → P.diagonalTwistEtale T i ⟶ P.diagonalTwistEtale T (i + j)
  | 0 => 𝟙 _
  | j + 1 => P.ordinaryFiniteEtaleHyperplaneProductMap T h i j ≫
      (Etale.derivedTensorSingleUnitIso (P.diagonalTwistEtale T (i + j))).inv ≫
      ((Etale.ordinaryFiniteTensor P.Coefficient T).obj
        (P.diagonalTwistEtale T (i + j))).map h

/-- Every ordered pro-etale product is postcomposition by the exact comparison
of the constructed coefficient product morphism, with arbitrary input class.
Source: Stacks Tag 0FI5, the linear coefficient expansion of the Chern relation.
Proof: at exponent zero use the identity. At a successor apply the one-step
postcomposition formula, the induction hypothesis, and functoriality of comparison.
All indices are the published i+j, including the zero and successor conventions.
(blueprint: lem-pur-chern-cup-comparison). -/
theorem ordinaryFiniteHyperplaneProduct_postcompose (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : ordinaryFiniteCohomology P T i) (j : ℕ) :
    P.ordinaryFiniteHyperplaneProduct T h i α j =
      α ≫ (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (P.ordinaryFiniteEtaleHyperplaneProductMap T h i j) := by
  induction j with
  | zero =>
    exact ((congrArg (fun z ↦ α ≫ z)
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map_id
          (P.diagonalTwistEtale T i))).trans (Category.comp_id α)).symm
  | succ j ih =>
    dsimp only [ordinaryFiniteHyperplaneProduct, ordinaryFiniteEtaleHyperplaneProductMap]
    rw [ordinaryFiniteHyperplaneStep_postcompose P a, ih]
    simp only [Functor.map_comp, Category.assoc]

end WeilConjectures.PurityFiniteSetting
