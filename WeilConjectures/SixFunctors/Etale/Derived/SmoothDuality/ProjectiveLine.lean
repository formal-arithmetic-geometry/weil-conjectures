/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsLinear

/-!
# Smooth duality for the projective and the affine line

The projective-line adjunction `Rq_* ⊣ q^*(1)[2]` for `q : ℙ¹_S ⟶ S`, whose counit is the trace
`Rq_*(q^* N (1)[2]) ≅ N ⊗ᴸ Rq_* Λ(1)[2] ⟶ N` (blueprint `thm-amb-p1-adjunction`, a node of the
subsection `sk-prop-geo-p1-adjunction`, recorded here without proof), makes `q` satisfy smooth
duality in degree `-2`: the counit is linear, so the canonical tensor maps of `q` are
isomorphisms and `ω_q ≅ Λ(1)[2]`
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMapOfIsIso_of_adjunction`). The affine
line `𝔸¹_S ⟶ S` is the composite of the open immersion `𝔸¹_S ⟶ ℙ¹_S`, `x ↦ [x : 1]`, and of
`q`, so it satisfies smooth duality as well
(`AlgebraicGeometry.Etale.affineLineSmoothDuality`). This is the affine-line case of the proof
of `thm-asd-smooth-tensor` (through `cor-amb-affine-space-adjunction`).

## Main statements

- `AlgebraicGeometry.Etale.exists_rightDerivedLowerStarAdjunction_projectiveLine`
  (`thm-amb-p1-adjunction`)
- `AlgebraicGeometry.Etale.satisfiesSmoothDuality_projectiveLine`
- `AlgebraicGeometry.Etale.affineLineSmoothDuality`

## Implementation notes

The twist `Λ(1)` is not a datum of the coefficient ring here (smooth duality does not choose an
orientation), so `thm-amb-p1-adjunction` is stated with an unnamed object `T`, a locally
constant sheaf of free rank-one `Λ`-modules placed in degree `-2`, in place of `Λ_S(1)[2]`, and
an unnamed `t` in place of the trace. The blueprint states the projective-line computation over
a Noetherian base; the adjunction is
stated here over an arbitrary base, as `cor-amb-affine-space-adjunction`
(`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`). For the
proper morphism `q`, the direct image with compact support `Rq_!` is `Rq_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), compatibly with the
projection maps, which transports the adjunction to `Rq_!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Blueprint `thm-amb-p1-adjunction`: The full projective-line adjunction.

For the projection `q : ℙ¹_S ⟶ S`, with the exponent of `Λ` invertible on `S`, on the whole
derived categories of étale sheaves of `Λ`-modules,

`Rq_* ⊣ q^*(1)[2]`,

and the counit is the trace counit `ε` of `def-amb-p1-trace`: for every `N`,
`ε_N : Rq_*(q^* N (1)[2]) ≅ N ⊗ᴸ Rq_* Λ(1)[2] ⟶ N` is the inverse of the projection formula
followed by `1 ⊗ t_q`, for the trace `t_q : Rq_* Λ(1)[2] ⟶ Λ_S`.

Here `T = Λ_S(1)[2]` is a locally constant sheaf of free rank-one `Λ`-modules placed in degree
`-2`, the functor `q^*(-)(1)[2]` is `N ↦ q^* T ⊗ᴸ q^* N`, and the counit is
`AlgebraicGeometry.Etale.rightDerivedLowerStarLinearCounit` of `t = t_q`, built from the
projection formula `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` of `Rq_*`. This
is a node of the blueprint subsection `sk-prop-geo-p1-adjunction`. -/
theorem exists_rightDerivedLowerStarAdjunction_projectiveLine (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    ∃ (T : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_ : IsShiftedRankOneLocalSystem T 2)
      (t : (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((ProjectiveLine S ↘ S)^*[ModuleCat.{u + 1} Λ])).obj T) ⟶ 𝟙_ _)
      (adj : R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ]) ⊣
        L((ProjectiveLine S ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
          (derivedTensor (ModuleCat.{u + 1} Λ) (ProjectiveLine S)).obj
            ((L((ProjectiveLine S ↘ S)^*[ModuleCat.{u + 1} Λ])).obj T)),
      ∀ N, adj.counit.app N = rightDerivedLowerStarLinearCounit (ProjectiveLine S ↘ S) _ t N :=
  sorry

/-- **Smooth duality for the projective line.** For `q : ℙ¹_S ⟶ S`, with the exponent of `Λ`
invertible on `S`, the dualizing complex `ω_q` is a locally constant sheaf of free rank-one
`Λ`-modules placed in degree `-2`, and the canonical tensor maps `θ_{q,K}` are isomorphisms: the
counit of the projective-line adjunction (`thm-amb-p1-adjunction`) is linear, and so is its
transport along `Rq_! ≅ Rq_*`
(`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriek_adjunction_of_rightDerivedLowerStar`). -/
theorem satisfiesSmoothDuality_projectiveLine (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    SatisfiesSmoothDuality Λ (ProjectiveLine S ↘ S) 2 := by
  intro _
  obtain ⟨T, hT, t, adj, hadj⟩ := exists_rightDerivedLowerStarAdjunction_projectiveLine Λ S
  obtain ⟨t', adj', hadj'⟩ := exists_rightDerivedLowerShriek_adjunction_of_rightDerivedLowerStar
    (A := ModuleCat.{u + 1} Λ) (ProjectiveLine S ↘ S) _ t adj hadj
  obtain ⟨e⟩ := nonempty_dualizingComplex_iso_of_adjunction (A := ModuleCat.{u + 1} Λ)
    (ProjectiveLine S ↘ S) _ t' adj' hadj'
  exact ⟨(hT.leftDerivedUpperStar _).of_iso e.symm, fun K ↦
    (isIso_dualizingComplexTensorMapOfIsIso_of_adjunction (A := ModuleCat.{u + 1} Λ)
      (ProjectiveLine S ↘ S) _ t' adj' hadj' K).1⟩

/-- The standard chart `𝔸¹_S ⟶ ℙ¹_S`, `x ↦ [x : 1]`, with the affine line indexed by
`ULift (Fin 1)`. -/
noncomputable def affineLineToProjectiveLine (S : Scheme.{u}) :
    𝔸(ULift.{u} (Fin 1); S) ⟶ ProjectiveLine S :=
  (AffineSpace.reindexIso S (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1)))).hom ≫
    ProjectiveLine.affineChart S

instance (S : Scheme.{u}) : IsOpenImmersion (affineLineToProjectiveLine S) := by
  unfold affineLineToProjectiveLine
  infer_instance

@[reassoc (attr := simp)]
lemma affineLineToProjectiveLine_over (S : Scheme.{u}) :
    affineLineToProjectiveLine S ≫ ProjectiveLine S ↘ S = 𝔸(ULift.{u} (Fin 1); S) ↘ S := by
  rw [affineLineToProjectiveLine, Category.assoc, ProjectiveLine.affineChart_over,
    AffineSpace.reindexIso_hom, AffineSpace.reindex_over]

/-- **Smooth duality for the affine line.** For every scheme `S` on which the exponent of `Λ` is
invertible, the projection `𝔸¹_S ⟶ S` satisfies smooth duality in degree `-2`: it is the
composite of the open immersion `𝔸¹_S ⟶ ℙ¹_S` and of the projective line `ℙ¹_S ⟶ S`
(`AlgebraicGeometry.Etale.satisfiesSmoothDuality_projectiveLine`). -/
theorem affineLineSmoothDuality : AffineLineSmoothDuality Λ := by
  intro S _ _ _
  set j := affineLineToProjectiveLine S
  set q := ProjectiveLine S ↘ S
  have w : j ≫ q = 𝔸(ULift.{u} (Fin 1); S) ↘ S := affineLineToProjectiveLine_over S
  have : HasCompactification j := (Compactification.ofIsOpenImmersion _).hasCompactification
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); S) := .of_hom (𝔸(ULift.{u} (Fin 1); S) ↘ S)
  have : HasInvertibleExponent Λ (ProjectiveLine S) := .of_hom q
  obtain ⟨hωq, hθq⟩ := satisfiesSmoothDuality_projectiveLine Λ S
  have hθj (P) : IsIso (dualizingComplexTensorMap Λ j P) :=
    isIso_dualizingComplexTensorMap_of_isOpenImmersion j P
  refine ⟨?_, fun K ↦ isIso_dualizingComplexTensorMap_comp_of_forall Λ j q _ w hθj
    hωq.isInvertible K (hθq K)⟩
  obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_leftDerivedUpperStar Λ j q _ w (hθj _)
    (nonempty_dualizingComplex_iso_of_isOpenImmersion j)
  exact (hωq.leftDerivedUpperStar j).of_iso c.symm

end Etale

end AlgebraicGeometry
