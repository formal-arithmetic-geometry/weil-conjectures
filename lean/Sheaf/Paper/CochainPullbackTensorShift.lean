/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

/-! # Signed shift compatibility of the prescribed pullback comparison

Source: Stacks 07A4 and 0FNH, item-shift-tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe uC vC uD vD r
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor
namespace CategoryTheory.CochainPullback
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)


@[no_expose] private def moduleTensorComparison :
    (Functor.postcompose₂.obj f.L).obj (ordinaryTensor.{uC, vC, r} R) ⟶
      (((Functor.whiskeringLeft₂
        (SheafOfModules.KFlatFixedTensor.Modules.{uD, vD, r} S)).obj f.L).obj f.L).obj
          (ordinaryTensor.{uD, vD, r} S) where
  app M :=
    { app := fun N ↦ (k.mu M N).hom
      naturality := fun {N N'} b ↦ by
        change f.L.map (M ◁ b) ≫ (k.mu M N').hom =
          (k.mu M N).hom ≫ (f.L.obj M ◁ f.L.map b)
        simpa only [tensorHom_def, Functor.map_id, MonoidalCategory.id_whiskerRight,
          Category.id_comp] using k.naturality (𝟙 M) b }
  naturality {M M'} a := by
    apply NatTrans.ext
    funext N
    change f.L.map (a ▷ N) ≫ (k.mu M' N).hom =
      (k.mu M N).hom ≫ (f.L.map a ▷ f.L.obj N)
    simpa only [tensorHom_def, Functor.map_id, MonoidalCategory.whiskerLeft_id,
      Category.comp_id] using k.naturality a (𝟙 N)

/-- The prescribed comparison as a natural transformation of curried cochain tensors.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-cochain-pullback-tensor-shift). -/
def tensorComparisonNatTrans :
    (Functor.postcompose₂.obj (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S)
      f)).obj (totalTensor.{uC, vC, r} R) ⟶
      (((Functor.whiskeringLeft₂
        (CochainComplex (SheafOfModules.KFlatFixedTensor.Modules.{uD, vD, r} S) ℤ)).obj (pull.{r,
          uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).obj
          (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).obj
        (totalTensor.{uD, vD, r} S) where
  app P :=
    { app := fun Q ↦ ((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P
      Q).hom
      naturality := fun {Q Q'} b ↦ by
        change ((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).map (P ◁ b) ≫
          ((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P Q').hom =
          ((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P Q).hom ≫
            (((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).obj P ◁ ((pull.{r,
            uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).map b)
        simpa only [tensorHom_def, Functor.map_id, MonoidalCategory.id_whiskerRight,
          Category.id_comp] using
            (cochainComparison_monoidal.{r, uC, vC, uD, vD}
              (J := J) (K := K) (R := R) (S := S) f k).1 P Q P Q' (𝟙 P) b }
  naturality {P P'} a := by
    apply NatTrans.ext
    funext Q
    change ((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).map (a ▷ Q) ≫
      ((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P' Q).hom =
      ((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P Q).hom ≫
        (((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).map a ▷ ((pull.{r, uC,
        vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).obj Q)
    simpa only [tensorHom_def, Functor.map_id, MonoidalCategory.whiskerLeft_id,
      Category.comp_id] using
        (cochainComparison_monoidal.{r, uC, vC, uD, vD}
              (J := J) (K := K) (R := R) (S := S) f k).1 P Q P' Q a (𝟙 Q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComparisonNatTrans_eq
    [f.L.IsLeftAdjoint] : tensorComparisonNatTrans f k =
    HomologicalComplex.mapBifunctorComparisonNatTrans (moduleTensorComparison f k) (.up ℤ) := by
  let := f.moduleAdj.isLeftAdjoint
  apply NatTrans.ext
  funext P
  apply NatTrans.ext
  funext Q
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map f.L
  intro p q hpq
  change f.L.map _ ≫ ((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P
    Q).hom.f n =
    f.L.map _ ≫ HomologicalComplex.mapBifunctorComparisonX
      (c₁ := .up ℤ) (c₂ := .up ℤ) (moduleTensorComparison f k) (.up ℤ) P Q n
  rw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  apply (cancel_mono (((comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k) P
    Q).inv.f n)).1
  simp only [Category.assoc,
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  change _ = (k.mu (P.X p) (Q.X q)).hom ≫ _ ≫
    (tensorPullbackTotal f.L k.mu k.naturality P Q).f n
  simp only [tensorPullbackTotal,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc,
    Iso.hom_inv_id_assoc]
  exact Category.comp_id
    (f.L.map (HomologicalComplex.ιMapBifunctor P Q
      (ordinaryTensor.{uC, vC, r} R) (.up ℤ) p q n hpq))

/-- The canonical pullback tensor comparison commutes with each integer shift.
For the second input the total shift has the Koszul factor; the general additive
bifunctor comparison theorem preserves it. For the first input the summand equation
is unsigned. The summand formula identifies that general comparison with the
prescribed inverse of the contraction map, so both results concern the same map.
Source: Stacks 07A4 and 0FNH, item-shift-tensor.
(blueprint: lem-weil-pbc-cochain-pullback-tensor-shift). -/
theorem tensorComparison_commShift :
    (∀ P, NatTrans.CommShift
      (F₁ := (totalTensor.{uC, vC, r} R).obj P ⋙ (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R :=
        R) (S := S) f))
      (F₂ := (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f) ⋙ (totalTensor.{uD,
        vD, r} S).obj (((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)).obj P))
      ((tensorComparisonNatTrans f k).app P) ℤ) ∧
      (∀ Q, NatTrans.CommShift
        (F₁ := (totalTensor.{uC, vC, r} R).flip.obj Q ⋙ (pull.{r, uC, vC, uD, vD} (J := J) (K :=
          K) (R := R) (S := S) f))
        (F₂ := (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f) ⋙
          (totalTensor.{uD, vD, r} S).flip.obj (((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R :=
          R) (S := S) f)).obj Q))
        ((tensorComparisonNatTrans f k).flipApp Q) ℤ) := by
  let := f.moduleAdj.isLeftAdjoint
  rw [tensorComparisonNatTrans_eq]
  exact ⟨fun P ↦ inferInstance, fun Q ↦ inferInstance⟩

end CategoryTheory.CochainPullback

-- Restore Mathlib's original instance for importing modules.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
