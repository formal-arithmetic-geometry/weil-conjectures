/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Functor

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

/-- The presheaf of homotopy classes from free representables to the integer extension
of a nonnegative complex of abelian sheaves. It is constructed by preadditive Yoneda. -/
def freeRepresentableHomotopyPresheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v} ⋙ CochainComplex.singleFunctor _ 0 ⋙
    HomotopyCategory.quotient _ (.up ℤ)).op ⋙
      preadditiveYoneda.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((K.extend ComplexShape.embeddingUpNat)⟦(q : ℤ)⟧))

/-- Homotopy classes from free representables compute objectwise homology of any
nonnegative complex of abelian sheaves; injectivity and Ext are not involved.
Source: Stacks Project, Section 01FT and Tag 03F3 (Hom-sections identification);
Derived Categories, Tag 06XR (homotopy classes from a single object).
(blueprint: lem-weil-pbc-free-representable-homotopy-homology)

Proof: Sheafification adjunction, the free abelian adjunction, and Yoneda identify
maps from the free abelian sheaf on U to G with G(U), additively and naturally in
both U and G. Apply this in every degree of the extension of K by zero. The Hom
complex from the degree-zero free sheaf becomes the lifted section complex.
Homotopy classes of maps to the q-shift are cocycles modulo coboundaries, hence
homology of that Hom complex. Evaluation of presheaves and additive universe lift
are exact and preserve homology. Extension by zero preserves homology at every
nonnegative degree; at q = 0 the incoming differential is zero on both sides.
Naturality in U of the adjunctions, extension comparison, and homology comparison
makes these isomorphisms commute with every restriction. Assemble them into a
natural isomorphism. This also applies to the empty site and the zero complex. -/
theorem freeRepresentableHomotopyPresheaf_homology
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) :
    Nonempty
      (freeRepresentableHomotopyPresheaf J K q ⋙ AddCommGrpCat.uliftFunctor.{w, max u v} ≅
        (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (.up ℕ)).obj
          K).homology q ⋙ AddCommGrpCat.uliftFunctor.{max u w, v}) := by
  sorry
