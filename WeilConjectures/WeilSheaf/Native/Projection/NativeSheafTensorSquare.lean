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
import WeilConjectures.Tactic.ExactModProofs

/-! # The native sheaf tensor square under condensed realization -/

@[expose] public section

set_option Elab.async false
set_option trace.profiler true
set_option trace.profiler.threshold 500
set_option diagnostics true
set_option diagnostics.threshold 1000

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

omit [Fact (ringChar k₀ ≠ l)] in
lemma condensedRealizationUpperStarIso_hom_app_eq (M : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealizationUpperStarIso k₀ l g).hom.app M =
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv.app
          M.carrier := by
  dsimp only [condensedRealizationUpperStarIso]
  exact_mod_proofs Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom_app
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l g
      (comp_over g (Spec (CommRingCat.of k₀))))
    (adicUpperStarCompCondensedModIso l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) M

omit [Fact (ringChar k₀ ≠ l)] in
lemma condensedRealizationUpperStarIso_hom_eq :
    (condensedRealizationUpperStarIso k₀ l g).hom =
      Functor.whiskerLeft (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
        (adicUpperStarCompCondensedModIso l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv := by
  dsimp only [condensedRealizationUpperStarIso]
  exact_mod_proofs Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l g
      (comp_over g (Spec (CommRingCat.of k₀))))
    (adicUpperStarCompCondensedModIso l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))

/-- The inverse square is the adic square on the underlying carriers. -/
lemma condensedRealizationSheafTensor_inverse_square (M N : ProEtaleWeilSheaf k₀ l Y) :
    SheafPullTensorInverseSquare k₀ l g M N := by
  unfold SheafPullTensorInverseSquare PullTensorInverseSquare
  rw [condensedRealizationSheafTensorIso_inv_eq, condensedRealizationSheafTensorIso_inv_eq,
    condensedRealizationUpperStarIso_hom_eq]
  simp only [Functor.whiskerLeft_app, condensedRealization, Functor.comp_map, Functor.comp_obj,
    Endofunctor.IsoAlgebra.forget_obj, Endofunctor.IsoAlgebra.forget_map]
  have hm := eq_of_heq (nativePullSheafTensor_hom_app_hom_f k₀ l g M N)
  rw [hm]
  cast_proofs adicUpperStar_condensedRelativeTensor_square l
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    M.carrier N.carrier

/-- The native pullback tensor comparison and the condensed realization tensor comparison
commute with the pullback comparison. -/
lemma condensedRealizationSheafTensor_pull_square (M N : ProEtaleWeilSheaf k₀ l Y) :
    SheafPullTensorSquare k₀ l g M N :=
  sheafPullTensorSquare_of_inverse k₀ l g M N
    (condensedRealizationSheafTensor_inverse_square k₀ l g M N)

end AlgebraicGeometry.ProEtaleWeilSheaf
