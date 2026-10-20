/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.LisseCoefficientFiberComparisons
public import Sheaf.Paper.NormalizedFibreComparisons

/-!
# Naturality of coefficient comparisons under fibre paths

Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-coefficient-fibre-comparison-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

private def coefficientCategoryComparison (E L : Padic.FiniteCoefficientFields l K)
    (f : E ⟶ L) :
    (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E)).toFunctor ⋙
        lisseRationalScalarExtension l E.val Y L.val
          (IntermediateField.inclusion (leOfHom f)) ≅
      ((lisseCoefficientDiagramData l Y K).diagram.map f.toLoc).toFunctor ⋙
        (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq L)).toFunctor := by
  let D := lisseCoefficientDiagramData l Y K
  let T := (eqToHom (D.obj_eq E)).toFunctor
  let U := (eqToHom (D.obj_eq E).symm).toFunctor
  let V := (eqToHom (D.obj_eq L)).toFunctor
  let Q := lisseRationalScalarExtension l E.val Y L.val
    (IntermediateField.inclusion (leOfHom f))
  let R := (D.diagram.map f.toLoc).toFunctor
  have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have he := D.map_eq E L (leOfHom f)
  rw [hf] at he
  have h : U ⋙ R ⋙ V = Q := congrArg Cat.Hom.toFunctor he
  let cancel (C D : Cat.{u + 1, u + 2}) (h : C = D) :
      (eqToHom h).toFunctor ⋙ (eqToHom h.symm).toFunctor ≅ 𝟭 C := by
    cases h
    exact Functor.leftUnitor _
  exact Functor.isoWhiskerLeft T (eqToIso h.symm) ≪≫
    (Functor.associator T U (R ⋙ V)).symm ≪≫
      Functor.isoWhiskerRight (cancel _ _ (D.obj_eq E)) (R ⋙ V) ≪≫
        Functor.leftUnitor _

/-- Passing from rational models to the recorded coefficient categories preserves
compatibility with a fibre path.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-coefficient-fibre-comparison-naturality).
Proof: the category transports and their cancellation comparison do not depend on the
geometric point. Whisker the given rational square and use naturality of the target
path with this cancellation comparison. -/
theorem coefficientFiberRawComparison_path
    (S S' : ∀ E : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E.val Y ⥤ ModuleCat.{u + 1} E.val)
    (δ : ∀ E : Padic.FiniteCoefficientFields l K, S E ≅ S' E)
    (E L : Padic.FiniteCoefficientFields l K) (f : E ⟶ L)
    (e : S E ⋙ ModuleCat.extendScalars (algebraMap E.val K) ≅
      lisseRationalScalarExtension l E.val Y L.val
        (IntermediateField.inclusion (leOfHom f)) ⋙ S L ⋙
          ModuleCat.extendScalars (algebraMap L.val K))
    (e' : S' E ⋙ ModuleCat.extendScalars (algebraMap E.val K) ≅
      lisseRationalScalarExtension l E.val Y L.val
        (IntermediateField.inclusion (leOfHom f)) ⋙ S' L ⋙
          ModuleCat.extendScalars (algebraMap L.val K))
    (h : e ≪≫ Functor.isoWhiskerLeft
        (lisseRationalScalarExtension l E.val Y L.val
          (IntermediateField.inclusion (leOfHom f)))
        (Functor.isoWhiskerRight (δ L) (ModuleCat.extendScalars (algebraMap L.val K))) =
      Functor.isoWhiskerRight (δ E) (ModuleCat.extendScalars (algebraMap E.val K)) ≪≫ e') :
    lisseCoefficientFiberRawComparison l Y K S E L f e ≪≫
        Functor.isoWhiskerLeft
          ((lisseCoefficientDiagramData l Y K).diagram.map f.toLoc).toFunctor
          (Functor.isoWhiskerLeft
            (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq L)).toFunctor
            (Functor.isoWhiskerRight (δ L)
              (ModuleCat.extendScalars (algebraMap L.val K)))) =
      Functor.isoWhiskerLeft
        (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E)).toFunctor
        (Functor.isoWhiskerRight (δ E) (ModuleCat.extendScalars (algebraMap E.val K))) ≪≫
          lisseCoefficientFiberRawComparison l Y K S' E L f e' := by
  change transportCoefficientComparison _ _ _ _
      (coefficientCategoryComparison l Y K E L f) e ≪≫ _ =
    _ ≪≫ transportCoefficientComparison _ _ _ _
      (coefficientCategoryComparison l Y K E L f) e'
  exact transportCoefficientComparison_path _ _ _ _ _ e e' _ _ h

end AlgebraicGeometry.Scheme
