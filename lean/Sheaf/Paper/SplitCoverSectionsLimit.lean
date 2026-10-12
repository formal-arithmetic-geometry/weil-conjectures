/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Sectionwise gluing for a split cover

Source: Stacks Project, etale-cohomology.tex, proof of Lemma 095B,
and sites.tex, Definition 00VM
(blueprint: lem-weil-pbc-split-cover-sections-limit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, etale-cohomology.tex, proof of Lemma 095B,
lines 9982--9991, and sites.tex, Definition 00VM.
(blueprint: lem-weil-pbc-split-cover-sections-limit).

Proof: Base change the clopen coproduct Y by W → X. Its j-th piece is W,
using the inverse t j to i j ≫ f; its inclusion is the displayed pullback lift.
These inclusions cover W ×_X Y and have empty pairwise overlaps for distinct
indices. The self-overlap projections agree because the inclusions are monic.
The sheaf condition makes sections the equalizer of the two overlap maps.
Sections on the empty object are zero, by its empty covering. Thus every family
of sections on the pieces is compatible and glues uniquely. For any module M,
a family of linear maps from M to these section modules therefore glues to a
unique map to H(W ×_X Y); uniqueness of gluing proves additivity and scalar
linearity. This is exactly the limiting-fan property, also for the empty family.
-/
theorem splitCoverSectionsLimit
    {X Y : Scheme.{u}} {J : Type w} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (f : Y ⟶ X) (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y)
    (t : ∀ j, X ⟶ V j)
    (hcolim : IsColimit (Cofan.mk Y i))
    (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
    (hinv₂ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
    (hopens : ∀ j, AlgebraicGeometry.IsOpenImmersion (i j))
    (hclosed : ∀ j, AlgebraicGeometry.IsClosedImmersion (i j))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (W : X.Etale) :
    letI : ∀ j, IsOpenImmersion (i j) := hopens
    letI : ∀ j, IsIso (t j) := fun j ↦
      ⟨⟨i j ≫ f, hinv₁ j, hinv₂ j⟩⟩
    let s := fun j ↦ t j ≫ i j
    Nonempty (IsLimit (Fan.mk
      (H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)))
      (fun j ↦ H.obj.map (MorphismProperty.Over.homMk
        (A := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (s j))).obj W)
        (B := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
        (pullback.lift (𝟙 W.left) (W.hom ≫ s j)
          (by
            change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s j) ≫ f
            simp [s, Category.assoc, hinv₁ j]))
        (by simp)).op))) := by sorry

end AlgebraicGeometry
