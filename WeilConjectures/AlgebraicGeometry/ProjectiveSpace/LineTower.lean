/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver

/-!

# Towers of projective lines

For a scheme `S`, the *tower of projective lines* `Scheme.projectiveLineTower S d` is the
iterated relative projective line `ℙ¹_{ℙ¹_{⋯_{S}}}` (`d` times), the fibre product
`ℙ¹_S ×_S ⋯ ×_S ℙ¹_S`, as a scheme over `S`. Each step `ℙ¹_B ⟶ B` is proper and smooth of
relative dimension one, so the tower is proper over `S`. Over a field `k`, the affine space
`𝔸ᵈ_k` is open in the `d`-th step, and hence every affine scheme of finite type over `k` admits
an immersion into a tower of projective lines
(`AlgebraicGeometry.Scheme.exists_isImmersion_projectiveLineTower`).

This is the geometry behind the proof of the trace formula for Frobenius correspondences
(blueprint `sk-thm-tf-coefficient-morphism-formula`): the only compactification used is
`𝔸¹ ⊆ ℙ¹`, applied in each coordinate.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The *tower of projective lines* over `S`: `projectiveLineTower S 0 = S` and
`projectiveLineTower S (d + 1) = ℙ¹_{projectiveLineTower S d}`, as schemes over `S`. -/
noncomputable def projectiveLineTower (S : Scheme.{u}) : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | d + 1 => overProjectiveLine (projectiveLineTower S d)

variable (S : Scheme.{u})

@[simp]
lemma projectiveLineTower_zero : projectiveLineTower S 0 = Over.mk (𝟙 S) :=
  rfl

@[simp]
lemma projectiveLineTower_succ (d : ℕ) :
    projectiveLineTower S (d + 1) = overProjectiveLine (projectiveLineTower S d) :=
  rfl

instance (d : ℕ) : LocallyOfFiniteType (projectiveLineTower S d).hom :=
  sorry

instance (d : ℕ) : QuasiCompact (projectiveLineTower S d).hom :=
  sorry

instance (d : ℕ) : IsSeparated (projectiveLineTower S d).hom :=
  sorry

instance (d : ℕ) : IsProper (projectiveLineTower S d).hom :=
  sorry

/-- **Affine schemes embed into towers of projective lines**: an affine scheme of finite type
over a field `k` admits an immersion over `k` into some `projectiveLineTower (Spec k) d`, the
composite of a closed immersion into `𝔸ᵈ_k` and of the open immersion of `𝔸ᵈ_k` into
`ℙ¹_k ×_k ⋯ ×_k ℙ¹_k`. -/
theorem exists_isImmersion_projectiveLineTower {k : Type u} [Field k] {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ (d : ℕ) (ι : X ⟶ (projectiveLineTower (Spec (.of k)) d).left),
      IsImmersion ι ∧ ι ≫ (projectiveLineTower (Spec (.of k)) d).hom = f :=
  sorry

end AlgebraicGeometry.Scheme
