/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateLocalRootTensorsExt
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels

/-! # Root-normalized comparisons used by integral smooth purity
Source: blueprint def-coefficient-twists-detailed, finite-reduction clause. The
ordinary root comparison retains its normalization on every local pure tensor.
(blueprint: def-pur-adic-root-comparisons).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme

namespace WeilConjectures

section SingleTensor
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} C]

/-- The tensor comparison for a flat sheaf placed in degree zero, obtained from the
specified K-flat tensor counit, not a choice of an isomorphism.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
def adicPuritySingleTensor (F G : C) (hF : ObjectProperty.flat F) :
    (DerivedCategory.singleFunctor C 0).obj F ⊗
      (DerivedCategory.singleFunctor C 0).obj G ≅
        (DerivedCategory.singleFunctor C 0).obj (F ⊗ G) :=
  tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app F) (Iso.refl _) ≪≫
    DerivedCategory.QObjTensorSingleFunctorObjIso
      ((HomologicalComplex.single C (.up ℤ) 0).obj F)
      ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 hF) G ≪≫
    DerivedCategory.Q.mapIso (((tensorRight G).mapCochainComplexSingleFunctor 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app (F ⊗ G)).symm
/-- Ordinary ordered tensor powers, retaining the specified coefficient unit.
Source: blueprint positive twists (blueprint: def-pur-adic-root-comparisons). -/
def adicPurityPower (U L : C) : ℕ → C
  | 0 => U
  | 1 => L
  | d + 2 => adicPurityPower U L (d + 1) ⊗ L

/-- Ordered shifted derived powers in the affine-line presentation.
Source: blueprint positive twists (blueprint: def-pur-adic-root-comparisons). -/
def adicPurityShiftedPower (U L : C) : ℕ → DerivedCategory C
  | 0 => (DerivedCategory.singleFunctor C 0).obj U
  | d + 1 => adicPurityShiftedPower U L d ⊗
      ((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧

/-- The shift degrees in the successor step agree as integers.
Source: blueprint positive twists, shifted power comparison
(blueprint: def-pur-adic-root-comparisons).
Proof: cast the two natural-number successors to integers, distribute multiplication
by two, and reassociate integer addition. -/
theorem adicPurityDoubleSuccSucc (d : ℕ) :
    2 * ((d + 1 : ℕ) : ℤ) + 2 = 2 * ((d + 2 : ℕ) : ℤ) := by
  omega

/-- Tensor-counit construction of the positive shifted power comparison. The unit,
K-flat counit, and shift maps specify every component.
Source: blueprint positive twists (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityDiagonalGeneric (U L : C)
    (eU : (DerivedCategory.singleFunctor C 0).obj U ≅ 𝟙_ (DerivedCategory C))
    (hF : ∀ d : ℕ, ObjectProperty.flat (adicPurityPower U L d)) :
    (d : ℕ) → adicPurityShiftedPower U L d ≅
      ((DerivedCategory.singleFunctor C 0).obj (adicPurityPower U L d))⟦2 * (d : ℤ)⟧
  | 0 => (shiftFunctorZero _ ℤ).symm.app _
  | 1 => tensorIso eU (Iso.refl _) ≪≫ λ_ _
  | d + 2 =>
    tensorIso (adicPurityDiagonalGeneric U L eU hF (d + 1)) (Iso.refl _) ≪≫
      DerivedCategory.shiftTensorShiftIso C _ _ (2 * ((d + 1 : ℕ) : ℤ)) 2 ≪≫
      (shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ) + 2)).mapIso
        (adicPuritySingleTensor _ _ (hF (d + 1))) ≪≫
      eqToIso (congrArg (fun j : ℤ ↦
        ((DerivedCategory.singleFunctor C 0).obj (adicPurityPower U L (d + 2)))⟦j⟧)
        (adicPurityDoubleSuccSucc d))

end SingleTensor

/-- The generic diagonal with its concrete etale source and target types fixed.
This interface checks the derived tensor instances and constant-sheaf unit once.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityEtaleDiagonalModel (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (hF : ∀ d : ℕ, ObjectProperty.flat (adicPurityPower
      (Etale.ordinaryFiniteConstant A T) (finiteEtaleTateLine T N A hA) d)) (d : ℕ) :
    adicPurityShiftedPower (Etale.ordinaryFiniteConstant A T)
      (finiteEtaleTateLine T N A hA) d ≅
        (Etale.ordinaryFiniteDegreeZero A T
          (adicPurityPower (Etale.ordinaryFiniteConstant A T)
            (finiteEtaleTateLine T N A hA) d))⟦2 * (d : ℤ)⟧ :=
  adicPurityDiagonalGeneric (Etale.ordinaryFiniteConstant A T)
    (finiteEtaleTateLine T N A hA)
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) hF d

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})

/-- Finiteness of every positive coefficient quotient.
Source: blueprint finite coefficients (blueprint: def-pur-adic-root-comparisons). -/
instance adicPurityQuotientFinite : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The root comparison is unique with its specified action on all local root tensors.
Source: finite Tate site descent, root projection clause
(blueprint: def-pur-adic-root-comparisons).
Proof: existence is the first assertion of finite_tate_site_descent. On a primitive-root
pro-etale cover the displayed pure tensors generate the rank-one coefficient module. The
normalization forces agreement there; sheaf separatedness gives global uniqueness. -/
theorem adicPurityRootComparison_existsUnique (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    ∃! b : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d) ≅ finiteTateProSheaf l E n T d,
      IsFiniteTateSiteComparison l E n T r hA d b := by
  obtain ⟨b, hb, _⟩ := finite_tate_site_descent l E n
  refine ⟨b T hT r hA d, hb T hT r hA d, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply finiteTate_local_root_tensors_hom_ext l E n T hT r hA d
  intro U W v a z x hx
  exact (hb' U W v a z x hx).trans ((hb T hT r hA d U W v a z x hx).symm)

/-- The unique comparison fixed by the root projection on every pure tensor.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityRootComparison (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d) ≅ finiteTateProSheaf l E n T d :=
  (adicPurityRootComparison_existsUnique l E n T hT r hA d).choose

/-- Every positive root-line tensor power is flat when l is invertible on the scheme.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons).
Proof: use an etale primitive-root cover for the invertible exponent. The first root
line is free of rank one on this cover. All nonnegative tensor powers are again rank
one, including the zero power. Flatness descends along this cover. -/
theorem adicPurityEtalePower_flat (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    ObjectProperty.flat (finiteEtaleTateTwist T (l ^ (r + 1))
      (finiteTateCoefficient l E n) hA d) := by
  have hInv : ∀ t : T, IsUnit ((l ^ (r + 1) : ℕ) : T.presheaf.stalk t) := fun t ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t (by trivial)).hom
  exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    (finite_etale_torsion_twist_line T (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hInv (finiteTateCoefficient l E n) hA d).2.2.1

private theorem adicPurityPower_eq_finiteEtaleTateTwist
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (d : ℕ) :
    adicPurityPower (Etale.ordinaryFiniteConstant A T) (finiteEtaleTateLine T N A hA) d =
      finiteEtaleTateTwist T N A hA d := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more d _ ih =>
    change adicPurityPower _ _ (d + 1) ⊗ _ = finiteEtaleTateTwist T N A hA (d + 1) ⊗ _
    rw [ih]

/-- Flatness in the generic ordered-power presentation.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons).
Proof: induction on the power identifies this recursion with finiteEtaleTateTwist.Apply
 adicPurityEtalePower_flat to that identification. -/
theorem adicPurityEtaleGenericPower_flat (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    ObjectProperty.flat (adicPurityPower
      (Etale.ordinaryFiniteConstant (finiteTateCoefficient l E n) T)
      (finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) d) := by
  rw [adicPurityPower_eq_finiteEtaleTateTwist]
  exact adicPurityEtalePower_flat l E n T r hT hA d

/-- Full equality with the prescribed generic tensor-counit comparison.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
def IsAdicPurityEtaleDiagonal (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ)
    (e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T d ≅
        (Etale.ordinaryFiniteDegreeZero (finiteTateCoefficient l E n) T
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧) : Prop :=
  HEq e (adicPurityEtaleDiagonalModel (finiteTateCoefficient l E n) (l ^ (r + 1)) hA T
    (adicPurityEtaleGenericPower_flat l E n T r hT hA) d)

/-- Transport the diagonal over abstract coefficients before specializing the ring. -/
private theorem adicPurityEtaleDiagonal_generic_existsUnique
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (hF : ∀ d : ℕ, ObjectProperty.flat (adicPurityPower
      (Etale.ordinaryFiniteConstant A T) (finiteEtaleTateLine T N A hA) d)) (d : ℕ) :
    ∃! e : Etale.affineLinearBaseCoefficient A N hA T d ≅
        (Etale.ordinaryFiniteDegreeZero A T (finiteEtaleTateTwist T N A hA d))⟦2 * (d : ℤ)⟧,
      HEq e (adicPurityEtaleDiagonalModel A N hA T hF d) := by
  let U := Etale.ordinaryFiniteConstant A T
  let L := finiteEtaleTateLine T N A hA
  have hs : ∀ k : ℕ,
      Etale.affineLinearBaseCoefficient A N hA T k = adicPurityShiftedPower U L k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change Etale.affineLinearBaseCoefficient _ _ _ _ k ⊗
        (Etale.ordinaryFiniteDegreeZero A T L)⟦(2 : ℤ)⟧ =
          adicPurityShiftedPower U L k ⊗
            (Etale.ordinaryFiniteDegreeZero A T L)⟦(2 : ℤ)⟧
      exact congrArg (fun X ↦ X ⊗
        (Etale.ordinaryFiniteDegreeZero A T L)⟦(2 : ℤ)⟧) ih
  have ht := congrArg (fun F ↦
    (Etale.ordinaryFiniteDegreeZero A T F)⟦2 * (d : ℤ)⟧)
      (adicPurityPower_eq_finiteEtaleTateTwist A N hA T d).symm
  have hty :
      (Etale.affineLinearBaseCoefficient A N hA T d ≅
        (Etale.ordinaryFiniteDegreeZero A T (finiteEtaleTateTwist T N A hA d))⟦2 * (d : ℤ)⟧) =
      (adicPurityShiftedPower U L d ≅
        (Etale.ordinaryFiniteDegreeZero A T (adicPurityPower U L d))⟦2 * (d : ℤ)⟧) := by
    exact congrArg₂ (fun X Y ↦ X ≅ Y) (hs d) ht
  have transport {α β : Type _} (h : α = β) (b : β) : ∃! a : α, HEq a b := by
    cases h
    exact ⟨b, HEq.rfl, fun a ha ↦ eq_of_heq ha⟩
  exact transport hty (adicPurityEtaleDiagonalModel A N hA T hF d)

/-- The concrete etale presentation uses exactly the generic tensor-counit construction.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons).
Proof: induction identifies affineLinearBaseCoefficient with adicPurityShiftedPower,
and two-step induction identifies the ordinary root powers with finiteEtaleTateTwist.
Transport the specified generic diagonal across these equalities. The cast is
heterogeneously equal to that diagonal; transitivity of heterogeneous equality then
proves uniqueness. -/
theorem adicPurityEtaleDiagonal_existsUnique (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    ∃! e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T d ≅
        (Etale.ordinaryFiniteDegreeZero (finiteTateCoefficient l E n) T
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧,
      IsAdicPurityEtaleDiagonal l E n T r hT hA d e := by
  exact adicPurityEtaleDiagonal_generic_existsUnique
    (finiteTateCoefficient l E n) (l ^ (r + 1)) hA T
    (adicPurityEtaleGenericPower_flat l E n T r hT hA) d

/-- The concrete etale comparison, fixed by equality with the tensor-counit construction.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityEtaleDiagonal (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T d ≅
        (Etale.ordinaryFiniteDegreeZero (finiteTateCoefficient l E n) T
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧ :=
  (adicPurityEtaleDiagonal_existsUnique l E n T r hT hA d).choose

/-- The positive diagonal line, in fixed pro-etale coefficients, is compared to
the original finite twisting line using the specified root projections.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityProDiagonal (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hPow : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapDerivedCategory.obj
        (Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d) ≅
      ((DerivedCategory.singleFunctor _ 0).obj (finiteTateProSheaf l E n T d))⟦2 * (d : ℤ)⟧ :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapDerivedCategory.mapIso
      (adicPurityEtaleDiagonal l E n T r hPow hA d) ≪≫
    (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapDerivedCategory).commShiftIso
      (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapDerivedCategorySingleFunctor
           0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (adicPurityRootComparison l E n T hT r hA d))

/-- The usual scalar-extension unit on the original first root line, on sections.
Source: blueprint finite coefficient reduction (blueprint: def-pur-adic-root-comparisons). -/
def adicPurityFirstRootQuotient (W : T.ProEtᵒᵖ)
    (x : (purTwistIntegralOne T l E).val.obj W) :
    (purTwistFiniteOne T l E n).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E T n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient T l E n) (purTwistIntegralOne T l E))).app W)
    ((1 : (integralCoefficientCommRingSheaf l E T n).obj.obj W)
      ⊗ₜ[_, ((purTwistIntegralQuotient T l E n).hom.app W).hom] x)

/-- Semilinear quotient maps on the actual nonnegative integral root powers.
Source: blueprint finite coefficient reduction (blueprint: def-pur-adic-root-comparisons). -/
abbrev AdicPurityRootQuotients := ∀ d : ℕ,
  integralTwistLine l E T (d : ℤ) ⟶
    (scalarReductionRestriction l E T n).obj (finiteCoefficientTwist l E T n (d : ℤ))

/-- Complete normalization: the coefficient projection at zero, the actual root-line
quotient unit at one, and the pure-tensor formula on every subsequent power.
Source: blueprint finite coefficient reduction (blueprint: def-pur-adic-root-comparisons). -/
def IsAdicPurityRootQuotients (c : AdicPurityRootQuotients l E n T) : Prop :=
  (∀ (W : T.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj W),
    (c 0).val.app W a =
      (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app W a) ∧
  (∀ (W : T.ProEtᵒᵖ) (b : (purTwistIntegralConstant T l E).obj.obj W)
    (x : (purTwistZlModule T l).val.obj W),
    (c 1).val.app W (purTwistIntegralTensor T l E W b x) =
      adicPurityFirstRootQuotient l E n T W (purTwistIntegralTensor T l E W b x)) ∧
  ∀ (d : ℕ) (W : T.ProEtᵒᵖ)
    (x : (integralTwistLine l E T ((d + 1 : ℕ) : ℤ)).val.obj W)
    (y : (purTwistIntegralModule T l E).val.obj W),
    (c (d + 2)).val.app W
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted l E T) _ _ W x y) =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := integralCoefficientCommRingSheaf l E T n) _ _ W
        ((c (d + 1)).val.app W x) ((c 1).val.app W y)

/-- The normalized quotient family exists uniquely, so no quotient-line map is chosen
from a bare assertion of isomorphy.
Source: blueprint finite coefficient reduction (blueprint: def-pur-adic-root-comparisons).
Proof: signedTwistFirstReduction compares the completed scalar reduction of the first
line with the prescribed finite line, with exactly the displayed tensor-unit equation.
The positive scalar-extension comparison starts with the scalar unit at zero and this
comparison at one, and uses the binary tensor comparison recursively. Compose its maps
with scalarExtensionEmbedding; the unit and pure-tensor formulas give normalization.
For uniqueness at one, restrict completed scalars to the integral constants and identify
the underlying line with the original integral tensor. Its scalar-extension generators
are exactly the displayed root tensors. Equality at zero is the coefficient equation;
two-step induction and tensor generation give equality at every higher degree. No local
trivialization or invertibility hypothesis is used. -/
theorem adicPurityRootQuotients_existsUnique :
    ∃! c : AdicPurityRootQuotients l E n T, IsAdicPurityRootQuotients l E n T c := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let p := completedIntegralCommRingProjectionUnrestricted l E T n
  let L := purTwistIntegralModule T l E
  let N := purTwistFiniteOne T l E n
  obtain ⟨b, hb⟩ := signedTwistFirstReduction l E T n
  let B := SheafOfModules.positiveComparison.{u + 1, u, u + 1} p L N b
  let c : AdicPurityRootQuotients l E n T := fun k ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
        p (integralTwistLine l E T (k : ℤ)) ≫
      (scalarReductionRestriction l E T n).map (B k).hom
  have hc (k : ℕ) (W : T.ProEtᵒᵖ)
      (x : (integralTwistLine l E T (k : ℤ)).val.obj W) :
      (c k).val.app W x = (B k).hom.val.app W
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E T (k : ℤ)) W 1 x) := rfl
  have hnorm : IsAdicPurityRootQuotients l E n T c := by
    refine ⟨?_, ?_, ?_⟩
    · intro W a
      rw [hc]
      change (SheafOfModules.scalarExtensionUnitIso p).hom.val.app W
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E T 0) W 1 a) = _
      exact (SheafOfModules.scalarExtensionUnitIso_tmul.{u + 1, u, u + 1}
        p W 1 a).trans (one_mul ((p.hom.app W).hom a))
    · intro W a x
      rw [hc]
      exact hb W (purTwistIntegralTensor T l E W a x)
    · intro k W x y
      rw [hc, hc, hc]
      exact SheafOfModules.positiveComparison_tmul.{u + 1, u, u + 1}
        p L N b k W 1 x y
  refine ⟨c, hnorm, ?_⟩
  intro c' hnorm'
  have hfirst : c' 1 = c 1 := by
    let F := SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistIntegralCompletionMap T l E))
    have hF : F.map (c' 1) = F.map (c 1) := by
      apply (cancel_epi (integralForgetIso T l E).inv).mp
      apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
        (purTwistConstantIntegersMap T l E)
      intro W a x
      change (c' 1).val.app W (purTwistIntegralTensor T l E W a x) =
        (c 1).val.app W (purTwistIntegralTensor T l E W a x)
      exact (hnorm'.2.1 W a x).trans (hnorm.2.1 W a x).symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f ↦ f.val.app W x) hF
  funext k
  induction k using Nat.twoStepInduction with
  | zero =>
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (hnorm'.1 W a).trans (hnorm.1 W a).symm
  | one => exact hfirst
  | more k _ ih =>
    apply SheafOfModules.scalarTensor_hom_ext.{u + 1, u, u + 1} _ _
      (R := R)
    intro W x y
    calc
      _ = _ := hnorm'.2.2 k W x y
      _ = _ := ?_
      _ = _ := (hnorm.2.2 k W x y).symm
    rw [ih, hfirst]

/-- The root-normalized quotient family, fixed by its full section equations.
Source: blueprint finite coefficient reduction (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityRootQuotients :
    AdicPurityRootQuotients l E n T :=
  (adicPurityRootQuotients_existsUnique l E n T).choose

end WeilConjectures
