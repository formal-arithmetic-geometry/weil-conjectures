/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Compactification.Defs

/-!
# The projective line compactifies the affine line

Over a scheme `S`, the projection `p : 𝔸¹_S ⟶ S` factors as the standard open immersion
`j̄ : 𝔸¹_S ↪ ℙ¹_S`, `t ↦ [t : 1]` (`AlgebraicGeometry.ProjectiveLine.affineChart`), followed by
the proper projection `q : ℙ¹_S ⟶ S`; the complement of `j̄` is the section
`∞ : S ⟶ ℙ¹_S`, a closed immersion. So `(j̄, q)` is a compactification of `p`
(`AlgebraicGeometry.ProjectiveLine.affineLineCompactification`).

## Main definitions

- `AlgebraicGeometry.ProjectiveLine.affineLineCompactification`: the compactification
  `(j̄, q)` of `𝔸¹_S ⟶ S`.
- `AlgebraicGeometry.ProjectiveLine.affineLineCompactification'`: the same for the affine line
  `𝔸(ULift (Fin 1); S)` of the purity chapter.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveLine

variable (S : Scheme.{u})

/-- The point at infinity `∞ : S ⟶ ℙ¹_S` is a closed immersion: it is a section of the separated
morphism `ℙ¹_S ⟶ S`. -/
instance isClosedImmersion_infinity : IsClosedImmersion (infinity S) := by
  have : IsClosedImmersion (infinity S ≫ ProjectiveLine S ↘ S) := by
    rw [infinity_over]
    infer_instance
  exact IsClosedImmersion.of_comp (infinity S) (ProjectiveLine S ↘ S)

/-- Blueprint `pur9-def-projective-line`: The projective line over a base

The compactification `d_p = (j̄, q)` of the projection `p : 𝔸¹_S ⟶ S`: the standard open
immersion `j̄ : 𝔸¹_S ↪ ℙ¹_S`, `t ↦ [t : 1]` (`AlgebraicGeometry.ProjectiveLine.affineChart`),
followed by the proper projection `q : ℙ¹_S ⟶ S`. The complement of `j̄` is the image of the
section `∞ : S ⟶ ℙ¹_S` (`AlgebraicGeometry.ProjectiveLine.range_infinity`), a closed immersion
(`AlgebraicGeometry.ProjectiveLine.isClosedImmersion_infinity`). -/
noncomputable def affineLineCompactification : Compactification (𝔸(PUnit.{u + 1}; S) ↘ S) where
  Z := ProjectiveLine S
  g := ProjectiveLine S ↘ S
  i := affineChart S
  comm := (affineChart_over S).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

@[simp]
lemma affineLineCompactification_i : (affineLineCompactification S).i = affineChart S :=
  rfl

@[simp]
lemma affineLineCompactification_g :
    (affineLineCompactification S).g = ProjectiveLine S ↘ S :=
  rfl

/-- The complement of the open immersion of the compactification `(j̄, q)` is the section `∞`. -/
lemma range_infinity_eq_compl_range_affineLineCompactification_i :
    Set.range (infinity S) = (Set.range (affineLineCompactification S).i)ᶜ :=
  range_infinity S

/-- The identification `𝔸(ULift (Fin 1); S) ≅ 𝔸(PUnit; S)` of the two models of the affine
line. -/
noncomputable def affineLineIso : 𝔸(ULift.{u} (Fin 1); S) ≅ 𝔸(PUnit.{u + 1}; S) :=
  AffineSpace.reindexIso S (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1)))

/-- Blueprint `pur9-def-projective-line`: The projective line over a base

The compactification `(j̄, q)` of the projection `p : 𝔸¹_S ⟶ S` for the model
`𝔸¹_S = 𝔸(ULift (Fin 1); S)` of the affine line used in the purity chapter: the open immersion
is `𝔸(ULift (Fin 1); S) ≅ 𝔸(PUnit; S) ↪ ℙ¹_S`. -/
noncomputable def affineLineCompactification' :
    Compactification (𝔸(ULift.{u} (Fin 1); S) ↘ S) :=
  ((affineLineCompactification S).precomp (affineLineIso S).hom).copy
    (by simp [affineLineIso, AffineSpace.reindex_over])

@[simp]
lemma affineLineCompactification'_i :
    (affineLineCompactification' S).i = (affineLineIso S).hom ≫ affineChart S :=
  rfl

@[simp]
lemma affineLineCompactification'_g :
    (affineLineCompactification' S).g = ProjectiveLine S ↘ S :=
  rfl

end AlgebraicGeometry.ProjectiveLine
