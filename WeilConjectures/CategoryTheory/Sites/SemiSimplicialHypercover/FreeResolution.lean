/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Basic

/-!
# The free resolution attached to a hypercover

Let `U` be a semi-simplicial hypercover of a site `(C, J)` and `R` a ring. Write `R[V]` for the
sheafification of the free presheaf of `R`-modules `W ↦ R^{(Hom(W, V))}` on the presheaf
represented by `V`. The alternating sums of the face maps make
`⋯ ⟶ R[U₂] ⟶ R[U₁] ⟶ R[U₀]` a chain complex (`CategoryTheory.SemiSimplicialObject.freeComplex`),
augmented to the constant sheaf `R` (`CategoryTheory.SemiSimplicialObject.freeAugmentation`). The
main result is that this augmented complex is exact: a cycle is locally a boundary, as one sees by
choosing locally a vertex and coning off, inductively over the dimension, the finitely many
simplices involved, using the local lifting property of the hypercover.

Since `Hom(R[V], I) = I(V)`, applying `Hom(-, I)` for an injective sheaf `I` shows that the
cochain complex `C^•(U, I)` of sections of `I` is exact in positive degrees and that its degree
zero cocycles are the global sections of `I`.

## Main statements

- `CategoryTheory.SemiSimplicialObject.IsHypercover.exactAt_freeComplex`: the free complex is
  exact in positive degrees.
- `CategoryTheory.SemiSimplicialObject.IsHypercover.exact_freeAugmentation`,
  `CategoryTheory.SemiSimplicialObject.IsHypercover.epi_freeAugmentation`: it is a resolution of
  the constant sheaf `R`.
- `CategoryTheory.SemiSimplicialObject.IsHypercover.exactAt_cochainComplex_of_injective`: the
  cochain complex of an injective sheaf is exact in positive degrees.
- `CategoryTheory.SemiSimplicialObject.IsHypercover.exact_cochainComplex_zero_of_injective`:
  its degree zero cocycles are the global sections.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]

/-- The constant sheaf of `R`-modules with value `R`. -/
noncomputable abbrev constSheaf : Sheaf J (ModuleCat.{max u v} R) :=
  (constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)

/-- The free presheaf of `R`-modules `W ↦ R^{(Hom(W, V))}` on the presheaf represented by `V`. -/
noncomputable abbrev freeYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v} R :=
  uliftYoneda.{u} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)

/-- The free sheaf of `R`-modules `R[V]`, the sheafification of `W ↦ R^{(Hom(W, V))}`. -/
noncomputable abbrev freeSheaf : C ⥤ Sheaf J (ModuleCat.{max u v} R) :=
  freeYoneda R ⋙ presheafToSheaf J _

/-- The free complex `⋯ ⟶ R[U₂] ⟶ R[U₁] ⟶ R[U₀]` of a semi-simplicial object, with the
alternating sums of the face maps as differentials. -/
noncomputable def freeComplex (U : SemiSimplicialObject C) :
    ChainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ :=
  ChainComplex.of (fun n ↦ (freeSheaf J R).obj (U.obj n))
    (fun n ↦ ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • (freeSheaf J R).map (U.δ n i))
    (by sorry)

@[simp]
lemma freeComplex_X (U : SemiSimplicialObject C) (n : ℕ) :
    (U.freeComplex J R).X n = (freeSheaf J R).obj (U.obj n) := rfl

/-- The map of presheaves `R^{(Hom(W, V))} ⟶ R` summing the coefficients. -/
noncomputable def freeYonedaToConst (V : C) :
    (freeYoneda R).obj V ⟶ (Functor.const Cᵒᵖ).obj (ModuleCat.of R R) where
  app _ := ModuleCat.ofHom (Finsupp.linearCombination R (fun _ ↦ (1 : R)))
  naturality _ _ _ := by sorry

/-- The augmentation `R[U₀] ⟶ R` to the constant sheaf, induced by the maps of presheaves
`R^{(Hom(W, U₀))} ⟶ R` summing the coefficients. -/
noncomputable def freeAugmentation (U : SemiSimplicialObject C) :
    (U.freeComplex J R).X 0 ⟶ constSheaf J R :=
  (presheafToSheaf J _).map (freeYonedaToConst R (U.obj 0))

lemma freeComplex_d_freeAugmentation (U : SemiSimplicialObject C) :
    (U.freeComplex J R).d 1 0 ≫ U.freeAugmentation J R = 0 := sorry

namespace IsHypercover

variable {J R}
variable {U : SemiSimplicialObject C} (hU : U.IsHypercover J)
include hU

variable (R) in
/-- **The free complex of a hypercover is exact in positive degrees** (blueprint
`lem-weil-pbc-hypercover-free-resolution`). -/
theorem exactAt_freeComplex (n : ℕ) :
    (U.freeComplex J R).ExactAt (n + 1) := sorry

variable (R) in
/-- The free complex of a hypercover is exact at `R[U₀]`, augmented to the constant sheaf. -/
theorem exact_freeAugmentation :
    (ShortComplex.mk _ _ (U.freeComplex_d_freeAugmentation J R)).Exact := sorry

variable (R) in
/-- The augmentation of the free complex of a hypercover is an epimorphism. -/
theorem epi_freeAugmentation : Epi (U.freeAugmentation J R) := sorry

/-- **The cochain complex of an injective sheaf on a hypercover is exact in positive degrees**
(blueprint `lem-weil-pbc-hypercover-free-resolution`). -/
theorem exactAt_cochainComplex_of_injective (I : Sheaf J (ModuleCat.{max u v} R)) [Injective I]
    (n : ℕ) : (U.cochainComplex I.obj).ExactAt (n + 1) := sorry

/-- **The degree zero cocycles of an injective sheaf on a hypercover are its global sections**
(blueprint `lem-weil-pbc-hypercover-free-resolution`): if `T` is a terminal object, the sequence
`0 ⟶ I(T) ⟶ I(U₀) ⟶ I(U₁)` is exact. -/
theorem exact_cochainComplex_zero_of_injective (I : Sheaf J (ModuleCat.{max u v} R))
    [Injective I] {T : C} (hT : IsTerminal T) :
    (ShortComplex.mk (I.obj.map (hT.from (U.obj 0)).op) (U.cochainDifferential I.obj 0)
      (by sorry)).Exact ∧ Mono (I.obj.map (hT.from (U.obj 0)).op) := sorry

end IsHypercover

end CategoryTheory.SemiSimplicialObject
