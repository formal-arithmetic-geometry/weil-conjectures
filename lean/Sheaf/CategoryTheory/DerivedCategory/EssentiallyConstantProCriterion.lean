/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda

/-! # Hom-colimit criterion for an essentially constant pro-diagram

Source: Stacks Project, Categories, Lemma 05PY (implication (4) => (1))
(blueprint: lem-pur-essential-constant-pro-criterion-05py).
-/

@[expose] public section

universe uJp vJp uCp vCp

open CategoryTheory

namespace CategoryTheory

/-- The Hom-colimit bijections induced by `r` make `G` essentially constant with value `X`.
The cone maps are the preimages of the identity classes, and `r` retracts the leg at `j₀`.

Source: Stacks Project, Categories, Lemma 05PY, implication (4) => (1), dualized;
Lemma 05PZ, implication (4) => (1)
(blueprint: lem-pur-essential-constant-pro-criterion-05py).

Proof (using def-pc-essentially-constant-pro-diagram):
1. For each `j`, bijectivity with `W = G.obj j` gives the unique preimage `u_j` of the
   identity class at `j`. Postcomposition by `G.map a`, for `a : j ⟶ j'`, takes the two
   identity classes to the same class. Injectivity therefore makes the `u_j` natural.
2. Postcompose the defining equality for `u_j₀` by `r`. With `W = X`, both
   `u_j₀ ≫ r` and `𝟙 X` map to the class of `r` at `j₀`; injectivity gives the retraction.
3. The defining equality for `u_j` in the filtered colimit of sets is witnessed at a
   common earlier stage `k`, with maps `a : k ⟶ j₀` and `b : k ⟶ j`. It says
   `G.map b = G.map a ≫ r ≫ u_j`.
4. These natural cone maps, the given `j₀` and `r`, the retraction and the common-stage
   factorization are exactly the witnesses for `IsEssentiallyConstantProDiagram G X`.
   The construction also supplies the asserted identity-class characterization. -/
theorem homColimit_essentiallyConstantProDiagram
    {J : Type uJp} {C : Type uCp} [Category.{vJp} J] [Category.{vCp} C]
    [IsCofiltered J]
    (G : J ⥤ C) (X : C) (j₀ : J) (r : G.obj j₀ ⟶ X)
    (h : ∀ (W : C), Function.Bijective (fun φ : X ⟶ W ↦
      ((G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j₀) (r ≫ φ)))) :
    IsEssentiallyConstantProDiagram G X ∧
    ∃ (u : (Functor.const J).obj X ⟶ G),
      u.app j₀ ≫ r = 𝟙 X ∧
      (∀ (j : J),
        (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType (Opposite.op j₀)
            (r ≫ u.app j) =
          (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType (Opposite.op j)
            (𝟙 (G.obj j)))
    := by
  sorry

end CategoryTheory
