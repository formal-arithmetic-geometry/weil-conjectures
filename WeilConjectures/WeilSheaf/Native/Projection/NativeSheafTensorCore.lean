/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
public import WeilConjectures.WeilSheaf.Native.Projection.NativeSheafSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
import WeilConjectures.Tactic.ExactModProofs

/-! # The native sheaf tensor square under condensed realization -/

@[expose] public section

set_option Elab.async false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

lemma condensedRealizationSheafTensorIso_inv_eq (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (M N : ProEtaleWeilSheaf k₀ l X) :
    (condensedRealizationSheafTensorIso k₀ l X).inv.app (M, N) =
      (condensedRelativeTensorIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        M.carrier N.carrier).inv := by
  rw [condensedRealizationSheafTensorIso_inv_app]
  rfl

/-- The carrier formula with homogeneous source and target. -/
lemma projection_nativePullSheafTensor_carrier_eq (M N : ProEtaleWeilSheaf k₀ l Y) :
    (((nativePullSheafTensor k₀ l g).hom.app (M, N)).hom.f) =
      (adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
          N.carrier).hom.app M.carrier := by
  exact eq_of_heq (nativePullSheafTensor_hom_app_hom_f k₀ l g M N)

/-- The native tensor has the relative tensor as carrier. -/
lemma projection_nativeOpenSheafTensor_obj_carrier (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (M N : ProEtaleWeilSheaf k₀ l X) :
    ((nativeOpenSheafTensor k₀ l X).obj (M, N)).carrier =
      (Mod.tensorLeft N.carrier).obj M.carrier := rfl

/-- Transport along an arbitrary Frobenius-compatible functor on the geometric fibres.
The fibre map and the Frobenius comparison remain parameters throughout the calculation. -/
lemma projection_inverse_square_of_frobenius
    (f : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (e : adicUpperStar l f ⋙ WeilSheaf.frobeniusPullback k₀ l Z ≅
      WeilSheaf.frobeniusPullback k₀ l Y ⋙ adicUpperStar l f)
    (mu : nativeOpenSheafTensor k₀ l Y ⋙ Endofunctor.IsoAlgebra.mapOfNatIso e ≅
      (Endofunctor.IsoAlgebra.mapOfNatIso e).prod (Endofunctor.IsoAlgebra.mapOfNatIso e) ⋙
        nativeOpenSheafTensor k₀ l Z)
    (hmu : ∀ M N, ((mu.hom.app (M, N)).hom.f) =
      (adicUpperStarTensorLeftIso l f N.carrier).hom.app M.carrier)
    (M N : ProEtaleWeilSheaf k₀ l Y) :
    PullTensorInverseSquare (Endofunctor.IsoAlgebra.mapOfNatIso e)
      (condensedRealization k₀ l Z) (condensedRealization k₀ l Y)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
      (nativeOpenSheafTensor k₀ l Y) (nativeOpenSheafTensor k₀ l Z) mu
      (condensedRealizationSheafTensorIso k₀ l Y) (condensedRealizationSheafTensorIso k₀ l Z)
      (Functor.isoHComp (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso e).symm
        (adicUpperStarCompCondensedModIso l f).symm) M N := by
  unfold PullTensorInverseSquare
  rw [condensedRealizationSheafTensorIso_inv_eq, condensedRealizationSheafTensorIso_inv_eq]
  simp only [Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom_app,
    condensedRealization, Functor.comp_map, Functor.comp_obj,
    Endofunctor.IsoAlgebra.forget_obj, Endofunctor.IsoAlgebra.forget_map,
    Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier,
    projection_nativeOpenSheafTensor_obj_carrier]
  rw [hmu]
  cast_proofs adicUpperStar_condensedRelativeTensor_square l f M.carrier N.carrier

end AlgebraicGeometry.ProEtaleWeilSheaf
