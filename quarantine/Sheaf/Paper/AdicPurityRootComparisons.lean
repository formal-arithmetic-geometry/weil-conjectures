/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Full equality with the prescribed generic tensor-counit comparison.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
def IsAdicPurityEtaleDiagonal (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ)
    (e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T d ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧) : Prop :=
  HEq e (adicPurityDiagonalGeneric
        (Etale.ordinaryFiniteConstant (finiteTateCoefficient l E n) T)
        (finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA)
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
        (adicPurityEtaleGenericPower_flat l E n T r hT hA) d)

/-- The concrete etale presentation uses exactly the generic tensor-counit construction.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons).
Proof: unfold the ordinary root powers and affineLinearBaseCoefficient. Their recursion
is the generic recursion above. The tensor bifunctor is the same K-flat monoidal
  tensor.Heterogeneous
 equality then fixes the actual isomorphism, and implies uniqueness. -/
theorem adicPurityEtaleDiagonal_existsUnique (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    ∃! e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T d ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧,
      IsAdicPurityEtaleDiagonal l E n T r hT hA d e := by
  sorry

/-- The concrete etale comparison, fixed by equality with the tensor-counit construction.
Source: blueprint coefficient twists (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityEtaleDiagonal (r : ℕ)
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
    Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA T d ≅
        ((DerivedCategory.singleFunctor _ 0).obj
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
Proof: the displayed first-line map is the ordinary tensor unit. Its completed scalar
linearity follows after projecting to every finite quotient, using the defining completed
action on the root limit. Tensor this map for positive powers, and use the coefficient
projection for the zero power. The balanced relations give maps of sheaf modules. On a
primitive-root cover every line is free of rank one and these equations determine the
maps on a generator, proving existence and uniqueness after descent. -/
theorem adicPurityRootQuotients_existsUnique :
    ∃! c : AdicPurityRootQuotients l E n T, IsAdicPurityRootQuotients l E n T c := by
  sorry

/-- The root-normalized quotient family, fixed by its full section equations.
Source: blueprint finite coefficient reduction (blueprint: def-pur-adic-root-comparisons). -/
@[no_expose] def adicPurityRootQuotients :
    AdicPurityRootQuotients l E n T :=
  (adicPurityRootQuotients_existsUnique l E n T).choose

end WeilConjectures
