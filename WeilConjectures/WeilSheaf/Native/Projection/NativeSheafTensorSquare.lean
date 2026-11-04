/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar

/-! # The native sheaf tensor square under condensed realization -/

@[expose] public section

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

lemma condensedRealizationUpperStarIso_hom_app_eq (M : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealizationUpperStarIso k₀ l g).hom.app M =
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv.app
          M.carrier := by
  simp [condensedRealizationUpperStarIso, Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso]

/-- The native pullback tensor comparison and the condensed realization tensor comparison
commute with the pullback comparison. -/
lemma condensedRealizationSheafTensor_pull_square (M N : ProEtaleWeilSheaf k₀ l Y) :
    (condensedRealization k₀ l Z).map ((nativePullSheafTensor k₀ l g).hom.app (M, N)) ≫
      (condensedRealizationSheafTensorIso k₀ l Z).hom.app
        ((upperStar k₀ l g).obj M, (upperStar k₀ l g).obj N) ≫
      ((condensedRealizationUpperStarIso k₀ l g).inv.app M ⊗ₘ
        (condensedRealizationUpperStarIso k₀ l g).inv.app N) =
    (condensedRealizationUpperStarIso k₀ l g).inv.app
        ((nativeOpenSheafTensor k₀ l Y).obj (M, N)) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).map
          ((condensedRealizationSheafTensorIso k₀ l Y).hom.app (M, N)) ≫
      Functor.OplaxMonoidal.δ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
          ((condensedRealization k₀ l Y).obj M) ((condensedRealization k₀ l Y).obj N) := by
  let G := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
  let a := condensedRealizationUpperStarIso k₀ l g
  let nY := condensedRealizationSheafTensorIso k₀ l Y
  let nZ := condensedRealizationSheafTensorIso k₀ l Z
  have h : G.map (nY.inv.app (M, N)) ≫
      a.hom.app ((nativeOpenSheafTensor k₀ l Y).obj (M, N)) ≫
      (condensedRealization k₀ l Z).map ((nativePullSheafTensor k₀ l g).hom.app (M, N)) =
    Functor.OplaxMonoidal.δ G ((condensedRealization k₀ l Y).obj M)
        ((condensedRealization k₀ l Y).obj N) ≫
      (a.hom.app M ⊗ₘ a.hom.app N) ≫
      nZ.inv.app ((upperStar k₀ l g).obj M, (upperStar k₀ l g).obj N) := by
    dsimp only [a, nY, nZ]
    rw [condensedRealizationSheafTensorIso_inv_eq,
      condensedRealizationSheafTensorIso_inv_eq,
      condensedRealizationUpperStarIso_hom_app_eq,
      condensedRealizationUpperStarIso_hom_app_eq,
      condensedRealizationUpperStarIso_hom_app_eq]
    have hm := eq_of_heq (nativePullSheafTensor_hom_app_hom_f k₀ l g M N)
    change G.map _ ≫ _ ≫ (adicSheafEquivCondensedMod l _).functor.map
      (((nativePullSheafTensor k₀ l g).hom.app (M, N)).hom.f) = _
    rw [hm]
    exact adicUpperStar_condensedRelativeTensor_square l _ M.carrier N.carrier
  apply (cancel_epi (a.hom.app ((nativeOpenSheafTensor k₀ l Y).obj (M, N)))).1
  apply (cancel_epi (G.map (nY.inv.app (M, N)))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    tensorHom_comp_tensorHom, Iso.hom_inv_id_app, id_tensorHom_id, Category.comp_id,
    ← G.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtaleWeilSheaf
