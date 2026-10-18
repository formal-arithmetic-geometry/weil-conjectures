/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCover

/-!
# The coordinate hyperplane of projective space

The hyperplane `V(T_∗) ⊆ ℙ(Option n; S)` where the extra homogeneous coordinate `T_∗` vanishes
is the image of the *hyperplane embedding* `ℙ(n; S) ⟶ ℙ(Option n; S)`,
`[Tᵢ] ↦ [Tᵢ : 0]` (`AlgebraicGeometry.ProjectiveSpace.hyperplane`), defined by the coordinate
sections of the standard coordinate cover of `ℙ(n; S)` and the zero section. The preimage of the
standard open `D₊(Tᵢ)` is `D₊(Tᵢ)`, and that of `D₊(T_∗)` is empty.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.standardCoordinateCover`: the coordinate cover of `ℙ(n; S)`
  by the standard opens.
- `AlgebraicGeometry.ProjectiveSpace.hyperplane`: the hyperplane embedding.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The coordinate cover of `ℙ(n; S)` by its standard opens `D₊(Tᵢ)`, with ratios `Tⱼ / Tᵢ`. -/
noncomputable def standardCoordinateCover : ℙ(n; S).CoordinateCover n :=
  Scheme.CoordinateCover.ofProj _ (toProjInt n S) one_pos MvPolynomial.X
    (fun i ↦ MvPolynomial.X_mem_homogeneousSubmodule_one _ i) (iSup_standardOpen n S)

@[simp]
lemma standardCoordinateCover_U (i : n) :
    (standardCoordinateCover n S).U i = standardOpen n S i := rfl

/-- The zero section of degree one of a coordinate cover. -/
def _root_.AlgebraicGeometry.Scheme.CoordinateCover.zeroSection {X : Scheme.{u}} {ι : Type u}
    (𝒟 : X.CoordinateCover ι) : 𝒟.Section 1 where
  s _ := 0
  s_eq _ _ := by simp

/-- The sections defining the hyperplane embedding: the coordinates `Tᵢ`, and `0` for the extra
coordinate. -/
noncomputable def hyperplaneSections : Option n → (standardCoordinateCover n S).Section 1
  | none => (standardCoordinateCover n S).zeroSection
  | some i => (standardCoordinateCover n S).coord i

lemma span_hyperplaneSections (i : n) :
    Ideal.span (Set.range fun a ↦ (hyperplaneSections n S a).s i) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨some i, rfl⟩) ?_
  simp [hyperplaneSections, (standardCoordinateCover n S).ratio_self i]

/-- **The hyperplane embedding** `ℙ(n; S) ⟶ ℙ(Option n; S)`, `[Tᵢ] ↦ [Tᵢ : 0]`, onto the
hyperplane where the extra coordinate vanishes. -/
noncomputable def hyperplane : ℙ(n; S) ⟶ ℙ(Option n; S) :=
  Scheme.CoordinateCover.hom (hyperplaneSections n S) (span_hyperplaneSections n S)
    (ℙ(n; S) ↘ S)

@[reassoc (attr := simp)]
lemma hyperplane_over : hyperplane n S ≫ ℙ(Option n; S) ↘ S = ℙ(n; S) ↘ S :=
  Scheme.CoordinateCover.hom_over _ _ _

lemma nonvanishing_coord {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι) (i : ι) :
    (𝒟.coord i).nonvanishing = 𝒟.U i := by
  refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le i ?_)
  · rw [Scheme.CoordinateCover.coord_s, 𝒟.basicOpen_ratio]
    exact inf_le_right
  · rw [Scheme.CoordinateCover.coord_s, 𝒟.ratio_self, Scheme.basicOpen_of_isUnit _ isUnit_one]

/-- The preimage of `D₊(Tᵢ)` under the hyperplane embedding is `D₊(Tᵢ)`. -/
lemma hyperplane_preimage_standardOpen_some (i : n) :
    hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i) = standardOpen n S i := by
  rw [hyperplane, Scheme.CoordinateCover.preimage_hom_standardOpen]
  exact nonvanishing_coord _ i

/-- The hyperplane misses `D₊(T_∗)`. -/
lemma hyperplane_preimage_standardOpen_none :
    hyperplane n S ⁻¹ᵁ standardOpen (Option n) S none = ⊥ := by
  rw [hyperplane, Scheme.CoordinateCover.preimage_hom_standardOpen]
  refine le_bot_iff.mp (iSup_le fun j ↦ ?_)
  simp [hyperplaneSections, Scheme.CoordinateCover.zeroSection]

end AlgebraicGeometry.ProjectiveSpace
