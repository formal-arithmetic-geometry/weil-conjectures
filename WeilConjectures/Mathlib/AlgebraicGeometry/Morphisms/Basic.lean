/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Properties local at the source and coproducts

A property of morphisms of schemes which is local at the source holds for `coprod.desc f g`
if it holds for `f` and `g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A property local at the source holds for `coprod.desc f g` if it holds for `f` and `g`. -/
lemma IsZariskiLocalAtSource.coprodDesc (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} (hf : P f) (hg : P g) :
    P (coprod.desc f g) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (coprodOpenCover.{_, 0} X Y)]
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · simpa [coprodOpenCover] using hf
  · simpa [coprodOpenCover] using hg

end AlgebraicGeometry
