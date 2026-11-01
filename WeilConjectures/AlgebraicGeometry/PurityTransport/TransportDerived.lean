/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportTensor
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-derived-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Flat degree-zero objects compare with their actual derived tensor.
Source: Stacks 06YH (blueprint: def-pur-transport-derived-coordinates). -/
def singleTensor (c : Coefficient ell) (X : Scheme.{u})
    (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
    (hM : ObjectProperty.flat M) :
    (DerivedCategory.singleFunctor _ 0).obj M ⊗
      (DerivedCategory.singleFunctor _ 0).obj N ≅
        (DerivedCategory.singleFunctor _ 0).obj (M ⊗ N) :=
  tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M)
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatLeft _ _
      ((CochainComplex.kFlat_single_obj_iff_flat _ 0).2 hM) ≪≫
    DerivedCategory.Q.mapIso (DerivedCategory.moduleCup_singleTensorIso M N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (M ⊗ N)).symm

/-- A given ordinary line comparison induces the canonical shifted derived one.
Source: Cartesian twists (blueprint: def-pur-transport-derived-coordinates). -/
def derivedPull (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (e : (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y d) ≅ c.line ell X d) :
    (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor.obj
      (c.derivedLine ell Y d) ≅ c.derivedLine ell X d :=
  (Functor.commShiftIso (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor
    (self := (CondensedRing.derivedUpperStarLowerStarAdjunction
      (c.obj ell) f).leftAdjointCommShift ℤ) (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (((CondensedRing.upperStar (c.obj ell) f).singleFunctorCompLeftDerivedFunctorIso).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e)

/-- Multiplication of shifted Tate lines with the canonical even-shift tensorator.
Source: tensor twists (blueprint: def-pur-transport-derived-coordinates). -/
def derivedProduct (c : Coefficient ell) (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] (d e : ℕ) :
    c.derivedLine ell X d ⊗ c.derivedLine ell X e ≅ c.derivedLine ell X (d + e) :=
  DerivedCategory.shiftTensorShiftIso _
      ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X d))
      ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X e))
      (2 * (d : ℤ)) (2 * (e : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ) + 2 * (e : ℤ))).mapIso
      (singleTensor ell c X _ _ (line_flat ell c X d) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (lineProduct ell c X d e)) ≪≫
    eqToIso (by simp only [Coefficient.derivedLine, Nat.cast_add, mul_add])

end AlgebraicGeometry.ProEtale.PurityTransport
