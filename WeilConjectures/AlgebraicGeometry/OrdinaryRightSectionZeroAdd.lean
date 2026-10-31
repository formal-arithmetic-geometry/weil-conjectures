/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSystemImageData
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Operations and transitions of the normalized ordinary right image

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-ordinary-right-section-laws).

The comparison below is the prescribed composite, natural in the strict system.
Scalar restriction is represented by `coefficientRestrictionUnderlying`, whose section
functions are identities. No transition of the system is required to be invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace SheafOfModules

/-- The specified underlying comparison, as a natural isomorphism in the strict system.
Its component is exactly the composite of `rightEvaluation` and `rightUnderlying`.
Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-ordinary-right-section-laws). -/
def ordinaryRightSectionZeroAddComparison
    {T U : Scheme.{u}} (g : T ⟶ U) (O : Type (u + 1)) [CommRing O] (t : O)
    (B : CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O t
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))) (n : ℕ) :
    B.rightSystem ⋙ coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology U) (O := O) (ell := t) n ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology U) O t n ≅
      coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (O := O) (ell := t) n ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology T) O t n ⋙
          Scheme.proEtaleSheafDirectImage g (Type (u + 1)) :=
  Functor.isoWhiskerRight (B.rightEvaluation n)
      (coefficientUnderlying (J := Scheme.ProEt.topology U) O t n) ≪≫
    Functor.isoWhiskerLeft (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (O := O) (ell := t) n)
      (B.rightUnderlying n)

private theorem naturality_zero_add
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u + 1}) [F.Additive] [G.Additive]
    (α : F ⋙ CategoryTheory.forget _ ⟶ G ⋙ CategoryTheory.forget _) (N : A) :
    α.app N 0 = 0 ∧ ∀ x y : F.obj N, α.app N (x + y) = α.app N x + α.app N y := by
  have hn {P Q : A} (f : P ⟶ Q) (z : F.obj P) :
      α.app Q (F.map f z) = G.map f (α.app P z) :=
    ConcreteCategory.congr_hom (α.naturality f) z
  have hz : α.app N 0 = 0 := by
    simpa using hn (0 : N ⟶ N) 0
  refine ⟨hz, ?_⟩
  intro x y
  let z : F.obj (N ⊞ N) := F.map biprod.inl x + F.map biprod.inr y
  have hfst : F.map (biprod.fst : N ⊞ N ⟶ N) z = x := by
    simp [z, ← ConcreteCategory.comp_apply, ← F.map_comp]
  have hsnd : F.map (biprod.snd : N ⊞ N ⟶ N) z = y := by
    simp [z, ← ConcreteCategory.comp_apply, ← F.map_comp]
  have hsum := hn ((biprod.fst : N ⊞ N ⟶ N) + biprod.snd) z
  have hf := hn (biprod.fst : N ⊞ N ⟶ N) z
  have hs := hn (biprod.snd : N ⊞ N ⟶ N) z
  rw [hfst] at hf
  rw [hsnd] at hs
  have hsum' : α.app N (x + y) =
      G.map biprod.fst (α.app (N ⊞ N) z) + G.map biprod.snd (α.app (N ⊞ N) z) := by
    simpa only [Functor.map_add, AddCommGrpCat.hom_add_apply, hfst, hsnd] using hsum
  rw [← hf, ← hs] at hsum'
  exact hsum'

/-! Helper for the zero and addition laws.
(blueprint: new-ordinary-right-section-zero-add). -/
/-- This is the corresponding strictly smaller clause of the ordinary right-section laws.
Source: Zheng, Construction 4.1 and the ordinary system morphism preceding Lemma 4.10,
printed pp. 21--23.
Proof: at each object `V`, `B.right n` followed by sections at `V` and sections at the
base-changed object are additive functors to abelian groups, and the `V`-component of
`B.rightUnderlying n` is a natural transformation of their underlying set functors.
Naturality for the zero endomorphism gives preservation of zero; naturality for the
biproduct projections `fst`, `snd` and `fst + snd` at `F(inl) x + F(inr) y` gives
preservation of addition (`naturality_zero_add`). Composing with the sectionwise linear
map `(B.rightEvaluation n).hom.app M` gives both clauses.
(blueprint: new-ordinary-right-section-zero-add). -/
theorem ordinaryRightSectionZeroAdd
    {T U : Scheme.{u}} (g : T ⟶ U) (O : Type (u + 1)) [CommRing O] (t : O)
    (B : CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O t
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1))))
    (M : CoefficientSystem (J := Scheme.ProEt.topology T) O t) (n : ℕ) :
    (∀ V : U.ProEtᵒᵖ,
      ((ordinaryRightSectionZeroAddComparison g O t B n).hom.app M).hom.app V
          (0 : ((B.rightSystem.obj M).level n).val.obj V) =
        (0 : (M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))) ∧
    (∀ (V : U.ProEtᵒᵖ) (x y : ((B.rightSystem.obj M).level n).val.obj V),
      ((ordinaryRightSectionZeroAddComparison g O t B n).hom.app M).hom.app V (x + y) =
        @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
          (((ordinaryRightSectionZeroAddComparison g O t B n).hom.app M).hom.app V x) +
        @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
          (((ordinaryRightSectionZeroAddComparison g O t B n).hom.app M).hom.app V y)) := by
  have h (V : U.ProEtᵒᵖ) :
      ((B.rightUnderlying n).hom.app (M.level n)).hom.app V
          (0 : ((B.right n).obj (M.level n)).val.obj V) =
        (0 : (M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V)) ∧
      ∀ x y : ((B.right n).obj (M.level n)).val.obj V,
        ((B.rightUnderlying n).hom.app (M.level n)).hom.app V (x + y) =
          @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
            (((B.rightUnderlying n).hom.app (M.level n)).hom.app V x) +
          @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
            (((B.rightUnderlying n).hom.app (M.level n)).hom.app V y) := by
    let F : coefficientLevelModules (J := Scheme.ProEt.topology T) O t n ⥤
        AddCommGrpCat.{u + 1} :=
      B.right n ⋙ evaluation _ V ⋙ CategoryTheory.forget₂ _ AddCommGrpCat
    let G : coefficientLevelModules (J := Scheme.ProEt.topology T) O t n ⥤
        AddCommGrpCat.{u + 1} :=
      evaluation _ ((Scheme.proEtaleBaseChange g).op.obj V) ⋙
        CategoryTheory.forget₂ _ AddCommGrpCat
    let : F.Additive := by
      dsimp only [F, evaluation]
      infer_instance
    let : G.Additive := by
      dsimp only [G, evaluation]
      infer_instance
    let α : F ⋙ CategoryTheory.forget _ ⟶ G ⋙ CategoryTheory.forget _ :=
      { app N := ((B.rightUnderlying n).hom.app N).hom.app V
        naturality P Q f := by
          exact congrArg (fun k ↦ k.hom.app V) ((B.rightUnderlying n).hom.naturality f) }
    exact naturality_zero_add F G α (M.level n)
  constructor
  · intro V
    change ((B.rightUnderlying n).hom.app (M.level n)).hom.app V
      (((B.rightEvaluation n).hom.app M).val.app V 0) =
        (0 : (M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
    rw [map_zero]
    exact (h V).1
  · intro V x y
    change ((B.rightUnderlying n).hom.app (M.level n)).hom.app V
        (((B.rightEvaluation n).hom.app M).val.app V (x + y)) =
      @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
        (((B.rightUnderlying n).hom.app (M.level n)).hom.app V
          (((B.rightEvaluation n).hom.app M).val.app V x)) +
      @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
        (((B.rightUnderlying n).hom.app (M.level n)).hom.app V
          (((B.rightEvaluation n).hom.app M).val.app V y))
    rw [map_add]
    exact (h V).2 _ _

end SheafOfModules
