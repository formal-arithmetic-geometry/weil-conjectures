/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Functoriality of the Čech complex in the coefficients

Let `U : ι → C` be a family of objects of a category with finite products, and let
`cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` be the Čech complex functor. For an
additive functor `G : A ⥤ B` preserving products, applying `G` degreewise to the Čech complex of
a presheaf `P` gives the Čech complex of `P ⋙ G`.

When `C` has a terminal object `T`, the Čech complex of `P` is augmented by
`P(T) ⟶ ∏ᵢ P(U i)`, the product of the restriction maps.

## Main definitions

- `CategoryTheory.cechComplexFunctorMapIso`: the isomorphism
  `G(Č(U, P)) ≅ Č(U, P ⋙ G)`.
- `CategoryTheory.cechAugmentation`: the augmentation `P(T) ⟶ Č⁰(U, P)`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

namespace AlgebraicTopology

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  (G : A ⥤ B) [G.Additive]

/-- An additive functor commutes with the alternating coface map complex. -/
noncomputable def mapAlternatingCofaceMapComplexIso (Y : CosimplicialObject A) :
    (G.mapHomologicalComplex _).obj ((alternatingCofaceMapComplex A).obj Y) ≅
      (alternatingCofaceMapComplex B).obj (Y ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    simp [AlternatingCofaceMapComplex.obj, AlternatingCofaceMapComplex.objD,
      CosimplicialObject.δ])

@[simp]
lemma mapAlternatingCofaceMapComplexIso_hom_f (Y : CosimplicialObject A) (n : ℕ) :
    (mapAlternatingCofaceMapComplexIso G Y).hom.f n = 𝟙 _ :=
  rfl

end AlgebraicTopology

namespace Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] {A B : Type*} [Category* A] [Category* B]
  [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

/-- A functor preserving products commutes with the evaluation of presheaves on formal
coproducts. -/
noncomputable def evalOpCompIso (P : Cᵒᵖ ⥤ A) :
    (evalOp.{w} C A).obj P ⋙ G ≅ (evalOp.{w} C B).obj (P ⋙ G) :=
  NatIso.ofComponents (fun X ↦ asIso (piComparison G _)) (fun f ↦ by
    refine Pi.hom_ext _ _ fun i ↦ ?_
    simp [← G.map_comp])

@[simp]
lemma evalOpCompIso_hom_app (P : Cᵒᵖ ⥤ A) (X : (FormalCoproduct.{w} C)ᵒᵖ) :
    (evalOpCompIso G P).hom.app X = piComparison G _ :=
  rfl

end Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasProducts.{w} A] [HasProducts.{w} B]

section

variable (G : A ⥤ B) [G.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

/-- An additive functor `G` preserving products commutes with the Čech complex functor:
`G(Č(U, P)) ≅ Č(U, P ⋙ G)`. -/
noncomputable def cechComplexFunctorMapIso (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex _).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ G) :=
  AlgebraicTopology.mapAlternatingCofaceMapComplexIso G _ ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex B).mapIso
      (Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
        (FormalCoproduct.evalOpCompIso G P))

lemma cechComplexFunctorMapIso_hom_f (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexFunctorMapIso U G P).hom.f n = piComparison G _ := by
  simp [cechComplexFunctorMapIso]

end

variable {T : C} (hT : IsTerminal T)

/-- The augmentation `P(T) ⟶ Č⁰(U, P) = ∏ᵢ P(U i)` of the Čech complex, for a terminal
object `T`: the product of the restriction maps. -/
noncomputable def cechAugmentation (P : Cᵒᵖ ⥤ A) :
    P.obj (op T) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  Pi.lift fun _ ↦ P.map (hT.from _).op

@[reassoc (attr := simp)]
lemma cechAugmentation_π (P : Cᵒᵖ ⥤ A) (i) :
    cechAugmentation U hT P ≫ Pi.π _ i = P.map (hT.from _).op :=
  Pi.lift_π _ _

@[reassoc (attr := simp)]
lemma cechAugmentation_d (P : Cᵒᵖ ⥤ A) :
    cechAugmentation U hT P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 := by
  sorry

@[reassoc]
lemma cechAugmentation_naturality {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    cechAugmentation U hT P ≫ ((cechComplexFunctor U).map φ).f 0 =
      φ.app _ ≫ cechAugmentation U hT Q := by
  sorry

lemma map_cechAugmentation_comp (G : A ⥤ B) [G.Additive]
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G] (P : Cᵒᵖ ⥤ A) :
    G.map (cechAugmentation U hT P) ≫ (cechComplexFunctorMapIso U G P).hom.f 0 =
      cechAugmentation U hT (P ⋙ G) := by
  sorry

end CategoryTheory
