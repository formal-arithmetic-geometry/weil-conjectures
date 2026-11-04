/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomBidual
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Monoidal equivalences commute with internal homs, as bifunctors

Let `U : C ⥤ D` be a monoidal functor between monoidal closed categories which is an equivalence,
and `H : Cᵒᵖ ⥤ C ⥤ C` a bifunctor identified with the internal hom of `C`, naturally in the first
variable. Then `U` carries `H` to the internal hom of `D`
(`CochainComplex.BifunctorMapIso.ofMonoidal`): the comparison `U [A, B] ≅ [U A, U B]`
(`CategoryTheory.Functor.Monoidal.ihomObjIso`) is natural in both variables.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasCountableProducts C] [MonoidalCategory C]
  [MonoidalClosed C]
  {H : Cᵒᵖ ⥤ C ⥤ C} [∀ X, (H.obj X).Additive] [H.Additive]
  {D : Type*} [Category* D] [Preadditive D] [HasCountableProducts D] [MonoidalCategory D]
  [MonoidalClosed D]
  (U : C ⥤ D) [U.Additive] [∀ n : ℤ, PreservesLimitsOfShape (Discrete (HomComplex.Triplet n)) U]
  [U.Monoidal] [U.IsEquivalence]

/-- A monoidal equivalence `U` carries a bifunctor `H` identified with the internal hom
(`e a : H(a, -) ≅ [a, -]`, natural in `a`) to the internal hom:
`U H(a, b) ≅ U [a, b] ≅ [U a, U b]`. -/
noncomputable def BifunctorMapIso.ofMonoidal (e : ∀ a : C, H.obj (op a) ≅ ihom a)
    (he : ∀ {a a' : C} (f : a ⟶ a'), H.map f.op ≫ (e a).hom = (e a').hom ≫ MonoidalClosed.pre f) :
    BifunctorMapIso H MonoidalClosed.internalHom U where
  iso a b := U.mapIso ((e a).app b) ≪≫ Functor.Monoidal.ihomObjIso U a b
  naturality_left {a a'} f b := by
    have h := NatTrans.congr_app (he f) b
    dsimp at h
    change U.map _ ≫ U.map ((e a).hom.app b) ≫
        (Functor.LaxMonoidal.ihomComparison U a).natTrans.app b =
      (U.map ((e a').hom.app b) ≫ (Functor.LaxMonoidal.ihomComparison U a').natTrans.app b) ≫
        (MonoidalClosed.pre (U.map f)).app (U.obj b)
    rw [← U.map_comp_assoc, h, U.map_comp_assoc,
      Functor.LaxMonoidal.map_pre_app_comp_ihomComparison, assoc]
  naturality_right a {b b'} g := by
    change U.map _ ≫ U.map ((e a).hom.app b') ≫
        (Functor.LaxMonoidal.ihomComparison U a).natTrans.app b' =
      (U.map ((e a).hom.app b) ≫ (Functor.LaxMonoidal.ihomComparison U a).natTrans.app b) ≫
        (ihom (U.obj a)).map (U.map g)
    rw [← U.map_comp_assoc, (e a).hom.naturality g, U.map_comp_assoc, assoc]
    erw [(Functor.LaxMonoidal.ihomComparison U a).natTrans.naturality g]
    rfl

end CochainComplex
