/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryRestrictionUnderlying
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients

/-! Source endpoint transport for the finite Chern coordinate. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem constantInteger_ext_one (T : Scheme.{u}) (M : DiagonalAb T)
    (f g : (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ M)
    (h : f.hom.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1)) =
      g.hom.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1))) : f = g := by
  apply ((constantSheafAdj (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.isTerminalMkId T)).homEquiv _ _).injective
  apply (M.obj.obj (op (Scheme.ProEt.mk (𝟙 T)))).uliftZMultiplesAddEquiv.injective
  simp only [AddCommGrpCat.uliftZMultiplesAddEquiv_eq,
    AlgebraicGeometry.constantSheafAdj_homEquiv_eq]
  exact h

private theorem integerMap_one (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) (U : T.ProEtᵒᵖ) :
    (diagonalCoefficientIntegerMap T R).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
          (ULift.up 1)) = (1 : R.obj.obj U) := by
  change ((toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (diagonalCoefficientIntegerMap T R).hom).app U) (ULift.up 1) = _
  unfold diagonalCoefficientIntegerMap
  rw [toSheafify_sheafifyLift]
  change ((1 : ℤ) : R.obj.obj U) = 1
  exact Int.cast_one

/-- Source endpoint transport.  This is the coefficient-one calculation: the
finite quotient followed by the restricted evaluation comparison is the
integer coefficient map.  The proof is the coefficient-one section calculation,
additivity, and the constant-sheaf adjunction.
(blueprint: lem-diagonal-local-finite-source-endpoint-transport) -/
theorem finiteBoundary_source_endpoint
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) :
    let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
    let e := finiteBoundaryRestrictionUnderlying l T r n
    S.map (finiteQuotient l (ULift.{u} (Padic l)) T n) ≫
        S.map (e.inv.app (coefficient T (Arings l (ULift.{u} (Padic l)) T))) =
      S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n)) := by
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  let M := coefficient T (Arings l (ULift.{u} (Padic l)) T)
  change S.map _ ≫ S.map _ = S.map _
  rw [← S.map_comp]
  apply congrArg S.map
  apply (cancel_mono (k.coefficientForget.hom.app (op n))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  apply constantInteger_ext_one
  let U := op (Scheme.ProEt.mk (𝟙 T))
  let z := (toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
      (ULift.up 1)
  let x' := (finiteQuotient l (ULift.{u} (Padic l)) T n).hom.app U z
  let x := (e.inv.app M).hom.app U x'
  have hq := (finiteQuotient_existsUnique l (ULift.{u} (Padic l)) T n).exists.choose_spec
    U (ULift.up 1)
  have hx' : HEq x' (1 : (systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop))) := by
    simpa only [x', z, finiteQuotient, Int.cast_one] using hq
  have hx : HEq x x' := by
    change HEq ((eqToHom (r.underlying M n U).symm) x') x'
    exact finiteBoundary_cast_heq _ _
  change (k.coefficientForget.hom.app (op n)).hom.app U x =
    (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n)).hom.app U z
  rw [k.coefficient_one n U x (hx.trans hx')]
  exact (integerMap_one T (Scheme.purTwistFiniteRing T l n) U).symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
