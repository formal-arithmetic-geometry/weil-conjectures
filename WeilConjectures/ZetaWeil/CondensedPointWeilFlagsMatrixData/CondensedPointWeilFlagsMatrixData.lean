/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint

/-!
# Finite-free Frobenius matrix data on the condensed point

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 7:
finite-free matrix sub-step of the zero-dimensional Jordan filtration
(blueprint: lem-zl-condensed-point-weil-flags-matrix-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedPointWeilFlagsMatrixData

/-- The geometric Frobenius automorphism of the condensed geometric point.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 7
(blueprint: lem-zl-condensed-point-weil-flags-matrix-data). -/
noncomputable def pointFrobenius (D : FiniteFieldDatum.{u}) :
    Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  Scheme.Spec.mapIso (σ.toRingEquiv.toCommRingCatIso.op)

/-- The current condensed coefficient module category on the geometric point.
Source: latest blueprint, `sk-def-sf-weil-complexes`, Weil-module paragraph
(blueprint: lem-zl-condensed-point-weil-flags-matrix-data). -/
abbrev PointWeilModule (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] :=
  AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed.WeilModule
    (Profinite.padicAlgClRingObj ell) (pointFrobenius D)

/-- Evaluation coordinates for a finite-free condensed module on the point.
Source: latest blueprint, `def-weil-finite-coefficient-point`, evaluation at the geometric
point, specialized to the finite-free module
(blueprint: lem-zl-condensed-point-weil-flags-matrix-data). -/
noncomputable def pointFreeCoordinates (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (d : ℕ) :
    (CondensedQbarGeometricEvaluation.fieldFiber D.k ell).obj
      (Mod.finiteFree
        (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of D.k))) d) ≃ₗ[
          PadicAlgCl ell] (Fin d → PadicAlgCl ell) :=
  (((CondensedQbarGeometricEvaluation.fieldFiber D.k ell).mapBiproduct
      (fun _ : Fin d ↦
        Mod.regular
          (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of D.k)))) ≪≫
    ModuleCat.biproductIsoPi _).toLinearEquiv).trans
      (LinearEquiv.piCongrRight
        (fun _ ↦ CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k ell))

/-- The conjugated Frobenius isomorphism in the finite-free basis.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 7
(blueprint: lem-zl-condensed-point-weil-flags-matrix-data). -/
noncomputable def conjugateFrobenius
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (M : PointWeilModule D ell) (d : ℕ)
    (e : M.carrier ≅ Mod.finiteFree
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of D.k))) d) :
    Mod.finiteFree
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of D.k))) d ≅
      Mod.finiteFree
        (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of D.k))) d :=
  (CondensedRing.upperStarFiniteFreeIso (Profinite.padicAlgClRingObj ell)
      (pointFrobenius D).hom d).symm ≪≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (pointFrobenius D).hom).mapIso e.symm ≪≫ M.str ≪≫ e

end WeilConjectures.CondensedPointWeilFlagsMatrixData
