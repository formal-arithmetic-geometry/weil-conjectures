/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.ComonadStandardResolution
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The standard simplicial object of an adjunction and its contractions

Source: Stacks Project, Simplicial, Situation 08N9 and Lemmas 08NC and 08ND
(blueprint: lem-trf-adjunction-standard-simplicial-homotopy).
-/

@[expose] public section

universe vS vA uS uA

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.Adjunction

variable {S : Type uS} [Category.{vS} S] {A : Type uA} [Category.{vA} A]

/-- Postcompose the endofunctor-valued resolution by the right adjoint, retaining
naturality in the augmented object. Source: Stacks, Tag 08ND
(blueprint: lem-trf-adjunction-standard-simplicial-homotopy). -/
abbrev standardSimplicialRight (B : SimplicialObject (A ⥤ A)) (U : A ⥤ S) :
    SimplicialObject (A ⥤ S) :=
  B ⋙ (Functor.whiskeringRight A A S).obj U

/-- The actual right-adjoint image of the augmentation. Source: Stacks, Tag 08ND
(blueprint: lem-trf-adjunction-standard-simplicial-homotopy). -/
abbrev standardSimplicialRightAugmentation (B : SimplicialObject (A ⥤ A))
    (e : B ⟶ (SimplicialObject.const (A ⥤ A)).obj (𝟭 A)) (U : A ⥤ S) :
    standardSimplicialRight B U ⟶ (SimplicialObject.const (A ⥤ S)).obj U :=
  Functor.whiskerRight e ((Functor.whiskeringRight A A S).obj U) ≫
    (Functor.constComp _ (𝟭 A) ((Functor.whiskeringRight A A S).obj U)).hom

/-- Precompose the resolution by the left adjoint, retaining naturality in the
free object. Source: Stacks, Tag 08ND
(blueprint: lem-trf-adjunction-standard-simplicial-homotopy). -/
abbrev standardSimplicialFree (B : SimplicialObject (A ⥤ A)) (F : S ⥤ A) :
    SimplicialObject (S ⥤ A) :=
  B ⋙ (Functor.whiskeringLeft S A A).obj F

/-- The actual augmentation on free objects. Source: Stacks, Tag 08ND
(blueprint: lem-trf-adjunction-standard-simplicial-homotopy). -/
abbrev standardSimplicialFreeAugmentation (B : SimplicialObject (A ⥤ A))
    (e : B ⟶ (SimplicialObject.const (A ⥤ A)).obj (𝟭 A)) (F : S ⥤ A) :
    standardSimplicialFree B F ⟶ (SimplicialObject.const (S ⥤ A)).obj F :=
  Functor.whiskerRight e ((Functor.whiskeringLeft S A A).obj F) ≫
    (Functor.constComp _ (𝟭 A) ((Functor.whiskeringLeft S A A).obj F)).hom

/-- The standard resolution of an adjunction exists and its augmentations after
applying the right adjoint and on free objects are simplicial homotopy equivalences.
The sections and homotopies are natural in the parameter. In particular the first
section is the unit in degree zero and its degeneracy extension in every degree.
Source: Stacks, Situation 08N9 and Lemmas 08NC and 08ND
(blueprint: lem-trf-adjunction-standard-simplicial-homotopy).

Proof: (1) The triangle identities give both counit laws for G = FU and
comultiplication FηU; naturality of η at η gives coassociativity.
(2) Apply lem-trf-comonad-simplicial-object to this comonad. Evaluation gives the
terms, operators and augmentation naturally in a.
(3) On UG^(n+1)a use η at UG^(n+1)a as the left extra degeneracy, including
η at Ua in augmented degree -1. The right triangle gives its counit equation;
naturality of η with the counit, faces and degeneracies gives all remaining
extra-degeneracy identities.
(4) Apply lem-coef-simplicial-extra-degeneracy-prism. Its section is the displayed
unit followed by the unique operator [n] → [0]; its homotopy contracts the section
composite to the identity. In sets this has the usual Δ[1] cylinder interpretation
of lem-coef-extra-degeneracy-contraction.
(5) On G^(n+1)Fs set v = Fη_s and use G^(n+1)v as right extra degeneracy.
The left triangle gives εv = 1. Naturality of faces and degeneracies at v gives
the right extra-degeneracy identities.
(6) Reverse all ordinal indices; these become left extra degeneracies.
(7) Apply the same prism lemma and undo reversal. Replacing H_j by H_(n-j)
swaps endpoints and gives a homotopy from the identity to the section composite.
All operations are natural transformations, so this argument applies directly in
the two parameter functor categories without limits or additive hypotheses. -/
theorem exists_standardSimplicialHomotopy {F : S ⥤ A} {U : A ⥤ S} (adj : F ⊣ U) :
    ∃ (B : SimplicialObject (A ⥤ A))
      (e : B ⟶ (SimplicialObject.const (A ⥤ A)).obj (𝟭 A)),
      Comonad.IsStandardSimplicialResolution adj.toComonad B e ∧
      (∃ r : (SimplicialObject.const (A ⥤ S)).obj U ⟶ standardSimplicialRight B U,
        r ≫ standardSimplicialRightAugmentation B e U = 𝟙 _ ∧
        Nonempty (SimplicialObject.Homotopy
          (standardSimplicialRightAugmentation B e U ≫ r)
          (𝟙 (standardSimplicialRight B U))) ∧
        HEq (r.app (op ⦋0⦌)) (Functor.whiskerLeft U adj.unit) ∧
        (∀ n : ℕ, r.app (op ⦋n⦌) = r.app (op ⦋0⦌) ≫
          (standardSimplicialRight B U).map (SimplexCategory.isTerminalZero.from ⦋n⦌).op)) ∧
      (∃ l : (SimplicialObject.const (S ⥤ A)).obj F ⟶ standardSimplicialFree B F,
        l ≫ standardSimplicialFreeAugmentation B e F = 𝟙 _ ∧
        Nonempty (SimplicialObject.Homotopy
          (𝟙 (standardSimplicialFree B F))
          (standardSimplicialFreeAugmentation B e F ≫ l))) := by
  sorry

end CategoryTheory.Adjunction
