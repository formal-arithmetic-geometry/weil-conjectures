/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-! # Data for the normalized finite Tate-power presentation

The finite Tate powers on the small etale site used in the smooth-dualizing construction,
and the data of a normalized presentation of the diagonal Tate twists as shifted finite Tate
powers.

## Implementation details

The presentation `EtalePowerPresentation` is built inductively: at zero it is the zero-shift
unitor, and the successor step tensors the preceding comparison with the shifted root line,
moves the shifts outside the tensor with `derivedTensorShiftIso`, and uses
`singleFunctorObjTensorIso` for the flat Tate power followed by `etalePowerStep`. The `HEq`
conditions only transport endpoint presentations and fix the data of every factor uniquely.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing
open AlgebraicGeometry.Scheme
attribute [local irreducible] finiteEtaleTateTensorFamily

/-- The tensor product of the `d`-th etale Tate power with the Tate line. -/
abbrev etalePowerProduct (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates d ⊗
      finiteEtaleTateLine T P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates

/-- The left unitor of the etale Tate line in the sheaf monoidal structure. -/
def etalePowerUnitor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  λ_ (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates)

/-- The zero power-step is uniquely given by the tensor unitor `etalePowerUnitor`. -/
theorem existsUnique_etalePowerZero (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ∃! e : etalePowerProduct P T 0 ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates 1,
      HEq e (etalePowerUnitor P T) := by
  refine ⟨etalePowerUnitor P T, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- A positive sheaf tensor power is literally the preceding power tensor the line, so the
positive power-step is uniquely the identity. -/
theorem existsUnique_etalePowerPositive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (d : ℕ) :
    ∃! e : etalePowerProduct P T (d + 1) ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 2),
      HEq e (Iso.refl (etalePowerProduct P T (d + 1))) := by
  refine ⟨Iso.refl _, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The power-step comparison: the tensor unitor at zero and the identity thereafter. -/
def etalePowerStep (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (d : ℕ) → etalePowerProduct P T d ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 1)
  | 0 => (existsUnique_etalePowerZero P T).exists.choose
  | d + 1 => (existsUnique_etalePowerPositive P T d).exists.choose

/-- Every nonnegative finite Tate power is flat, including the coefficient unit. -/
theorem etalePowerFlat (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ) :
    ObjectProperty.flat (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d) := by
  let e := finiteEtaleTateTensorFamily T P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) P.Coefficient
    P.diagonalExponent_annihilates hT
  have h := (e.tensorInverse (d : ℤ)).flat
  dsimp only [e] at h
  rw [finiteEtaleTateTensorFamily_obj] at h
  exact h

/-- The finite Tate sheaf placed in degree zero. -/
abbrev etaleSingle (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d)

/-- The derived tensor product on the small etale site, with coefficients explicit. -/
abbrev etaleTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T

/-- A normalized family of comparisons between the diagonal Tate twists and the shifted
finite Tate powers, built at each successor from the tensor map, the shift comparison, the flat
single-complex comparison and the sheaf-power step. -/
structure EtalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) where
  comparison : (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧
  normalized :
    letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    HEq (comparison 0) (((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm) ∧
      ∀ d : ℕ,
        ∃ (e₁ : P.diagonalTwistEtale T (d + 1) ≅
              ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧))
          (e₂ : ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧) ≅
              (((etaleTensor P T).obj (etaleSingle P T d)).obj
                (etaleSingle P T 1))⟦2 * (d : ℤ) + 2⟧)
          (e₃ : ((etaleTensor P T).obj (etaleSingle P T d)).obj (etaleSingle P T 1) ≅
              (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d))
          (e₄ : (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d) ≅
              etaleSingle P T (d + 1)),
          HEq e₁ ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
            ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso (comparison d)) ∧
          HEq e₂ (Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
            (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2) ∧
          HEq e₃ (Etale.singleFunctorObjTensorIso
            (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
            (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates d)
            (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates) (etalePowerFlat P T hT d)) ∧
          HEq e₄ ((DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ∧
          comparison (d + 1) = e₁ ≪≫ e₂ ≪≫
            (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso (e₃ ≪≫ e₄) ≪≫
            eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
              (PurityFiniteSetting.frameDegreeNext d))

/-- One normalized successor comparison, using the four prescribed factors and the degree
equality. -/
def etalePowerPresentationNext (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ)
    (e : P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧) :
    P.diagonalTwistEtale T (d + 1) ≅ (etaleSingle P T (d + 1))⟦2 * ((d + 1 : ℕ) : ℤ)⟧ :=
  ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
    ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso e) ≪≫
  Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
    (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2 ≪≫
  (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso
    (Etale.singleFunctorObjTensorIso
      (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
      (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates d)
      (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates) (etalePowerFlat P T hT d) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ≪≫
  eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
    (PurityFiniteSetting.frameDegreeNext d))

end AdicSmoothDualizing
end WeilConjectures
