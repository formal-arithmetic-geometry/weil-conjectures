/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Projectivity of an abelian variety and a symmetric ample line bundle

An abelian variety `A` over a field `K` is projective: it carries an ample line bundle. This
is the one input of the degree chapter that is specific to abelian varieties, and it is stated
here without proof.

Granting it, `A` carries an ample line bundle which is moreover *symmetric*, that is, is fixed
by pullback along the inversion `[-1] : A ⟶ A`. Indeed, if `L₀` is ample then so is
`[-1]^* L₀`, since `[-1]` is an isomorphism, hence so is `L := L₀ ⊗ [-1]^* L₀`; and
`[-1]^* L ≅ [-1]^* L₀ ⊗ ([-1] ∘ [-1])^* L₀ = [-1]^* L₀ ⊗ L₀ ≅ L`, because `[-1] ∘ [-1] = 𝟙`.
A symmetric ample line bundle is what the theorem of the cube is applied to in order to compute
the degree of the isogeny `[n]`.

Throughout, `A` is a group scheme in the sense of
`WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian`: an object `G : Over (Spec (.of K))`
with a `CategoryTheory.GrpObj G` structure, so that the underlying scheme is `G.left` and the
inversion `[-1]` is `(CategoryTheory.GrpObj.zpow G (-1)).left`.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety.IsSymmetric`: a sheaf of modules `L` on a group scheme
  `G` is symmetric if `[-1]^* L ≅ L` (blueprint: glue item 12 of `sec:deg-cost`).

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple` — **an abelian variety is
  projective**: it carries an ample line bundle. This is `sorry` by design; see the
  implementation notes below (blueprint: `prop:deg-abelian-projective`).
- `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple_isSymmetric` — **an abelian
  variety carries a symmetric ample line bundle** (blueprint: `prop:deg-symmetric-ample`).

## Implementation notes

* **A deliberate `sorry`.** `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple` is
  stated and not proved, exactly as `WeilConjectures.AlgebraicGeometry.ChowLemma` states
  Chow's lemma without proving it. It is an open obligation of the degree chapter, and the one
  obligation of that chapter which is specific to abelian varieties: no general-purpose
  Mathlib development will supply it. The classical route is
  [Mumford][MumfordAbelianVarieties], §6. Choose an affine open `U ⊆ A` containing the
  identity `e`. Since `A` is smooth and the complement of an affine open in a smooth variety
  is of pure codimension one, the reduced complement `D := A \ U` is an effective divisor with
  `A \ Supp D = U` affine; one then shows that `𝒪_A(3 D)` is very ample, translating `D` by
  the theorem of the square to separate any pair of points and any tangent vector. The
  argument uses only the group law and the affineness of `U`, not the theorem of the cube,
  which is why it belongs to the degree chapter.

* **Everything else here is proved.**
  `AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple_isSymmetric` of course
  inherits the `sorry` above, and the further `sorry` of
  `AlgebraicGeometry.Scheme.Modules.IsAmple.tensorObj`, the permanence property
  `lem:deg-ample-basic` (1) that is left open in
  `WeilConjectures.AlgebraicGeometry.Ample`. Neither is a gap in the argument given here.

* **Generality.** The blueprint chapter works throughout over an algebraically closed field.
  Nothing in either statement below needs that, and neither does the classical proof of
  projectivity, so both are stated over an arbitrary field `K`; a consumer working over an
  algebraically closed field can use them unchanged.

* `[-1]` is `(CategoryTheory.GrpObj.zpow G (-1)).left`, and is an isomorphism because it is its
  own inverse, `AlgebraicGeometry.IsAbelianVariety.zpow_neg_one_comp_self`. Being an
  isomorphism it is an immersion, which is what
  `AlgebraicGeometry.Scheme.Modules.IsAmple.pullback_of_isImmersion` needs in order to make
  `[-1]^* L₀` ample.

## References

* D. Mumford, *Abelian Varieties*, §6.
* J. S. Milne, *Abelian Varieties*, I §7.

## Blueprint

This file states `prop:deg-abelian-projective` and proves `prop:deg-symmetric-ample` of
`curve_estimates/28_degree_of_the_isogeny.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.IsAbelianVariety

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G]

section Inversion

/-- **`[-1]` is its own inverse**: `[-1] ∘ [-1] = [1] = 𝟙`. -/
lemma zpow_neg_one_comp_self : GrpObj.zpow G (-1) ≫ GrpObj.zpow G (-1) = 𝟙 G := by
  rw [GrpObj.zpow_comp_zpow, show (-1 : ℤ) * (-1) = 1 by norm_num, GrpObj.zpow_one]

/-- `[-1]` is an isomorphism of group schemes, being its own inverse. -/
instance isIso_zpow_neg_one : IsIso (GrpObj.zpow G (-1)) :=
  ⟨GrpObj.zpow G (-1), zpow_neg_one_comp_self G, zpow_neg_one_comp_self G⟩

/-- On underlying schemes, `[-1] ∘ [-1] = 𝟙`. -/
lemma left_zpow_neg_one_comp_self :
    (GrpObj.zpow G (-1)).left ≫ (GrpObj.zpow G (-1)).left = 𝟙 G.left := by
  rw [← Over.comp_left, zpow_neg_one_comp_self, Over.id_left]

/-- The inversion `[-1] : A ⟶ A` of a group scheme is an isomorphism of schemes. -/
instance isIso_left_zpow_neg_one : IsIso (GrpObj.zpow G (-1)).left :=
  ⟨(GrpObj.zpow G (-1)).left, left_zpow_neg_one_comp_self G, left_zpow_neg_one_comp_self G⟩

end Inversion

/-- A sheaf of modules `L` on a group scheme `A` is **symmetric** if it is fixed by pullback
along the inversion, that is, if `[-1]^* L ≅ L`.

This is intended for a line bundle `L`; invertibility is not part of the definition, and is
carried as a hypothesis by the statements that need it.
(blueprint: glue item 12 of `sec:deg-cost`) -/
def IsSymmetric (L : G.left.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback (GrpObj.zpow G (-1)).left).obj L ≅ L)

variable [IsAbelianVariety G]

/-- **An abelian variety is projective**: it carries an ample line bundle.

This is `sorry` by design; see the implementation notes of this file. The classical proof is
[Mumford][MumfordAbelianVarieties], §6: the complement of an affine open neighbourhood `U` of
the identity is an effective divisor `D`, and `𝒪(3 D)` is very ample by the theorem of the
square.
(blueprint: `prop:deg-abelian-projective`) -/
theorem exists_invertible_isAmple :
    ∃ L : G.left.Modules, L.Invertible ∧ L.IsAmple :=
  sorry

/-- **An abelian variety carries a symmetric ample line bundle.** If `L₀` is an ample line
bundle on `A`, then `L := L₀ ⊗ [-1]^* L₀` is ample, and it is symmetric because
`[-1] ∘ [-1] = 𝟙`.
(blueprint: `prop:deg-symmetric-ample`) -/
theorem exists_invertible_isAmple_isSymmetric :
    ∃ L : G.left.Modules, L.Invertible ∧ L.IsAmple ∧ IsSymmetric G L := by
  obtain ⟨L₀, hL₀, hL₀a⟩ := exists_invertible_isAmple G
  have hproper : IsProper (G.left ↘ Spec (.of K)) := IsAbelianVariety.isProper
  set e : G.left ⟶ G.left := (GrpObj.zpow G (-1)).left
  have hpb : ((Scheme.Modules.pullback e).obj L₀).Invertible := hL₀.pullback e
  refine ⟨L₀ ⊗ (Scheme.Modules.pullback e).obj L₀, hL₀.tensorObj hpb,
    IsAmple.tensorObj hL₀ hpb hL₀a (IsAmple.pullback_of_isImmersion K e hL₀ hL₀a), ⟨?_⟩⟩
  -- `[-1]^* (L₀ ⊗ [-1]^* L₀) ≅ [-1]^* L₀ ⊗ ([-1] ∘ [-1])^* L₀ ≅ [-1]^* L₀ ⊗ L₀ ≅ L₀ ⊗ [-1]^* L₀`
  exact (Functor.Monoidal.μIso (Scheme.Modules.pullback e) _ _).symm ≪≫
    tensorIso (Iso.refl _)
      ((Scheme.Modules.pullbackTriangle (left_zpow_neg_one_comp_self G)).app L₀ ≪≫
        (Scheme.Modules.pullbackId G.left).app L₀) ≪≫ β_ _ _

end AlgebraicGeometry.IsAbelianVariety
