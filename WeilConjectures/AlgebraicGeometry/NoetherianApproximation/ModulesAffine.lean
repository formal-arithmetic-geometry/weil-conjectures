/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix

/-!
# Modules of finite presentation on a cofiltered limit of affine schemes

Let `{Eⱼ}` be a cofiltered system of affine schemes with limit `X = lim Eⱼ`. Then the category of
modules of finite presentation on `X` is the colimit of the categories of modules of finite
presentation on the `Eⱼ` (Stacks, Tag 01ZR, affine case; EGA IV₃, 8.5.2):

- every module of finite presentation on `X` is the pullback of one on some `Eⱼ`
  (`AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_of_isLimit_of_isAffine`);
- two morphisms between modules of finite presentation on `Eⱼ` which agree after pullback to `X`
  agree after pullback to some later stage
  (`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_eq_of_isLimit_of_isAffine`);
- every morphism between the pullbacks to `X` of modules of finite presentation on `Eⱼ` is the
  pullback of a morphism defined over some later stage
  (`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_eq_of_isLimit_of_isAffine'`).

## Proof

On an affine scheme a module of finite presentation is the cokernel of a morphism
`𝒪^I ⟶ 𝒪^J` of free modules of finite rank, i.e. of a matrix of global functions
(`Modules/FreeMatrix.lean`), and pullback sends this cokernel to the cokernel of the matrix of
pulled back functions. The global sections of `X` are the colimit of those of the `Eⱼ`
(`AlgebraicGeometry.exists_appTop_π_eq_of_isLimit`, `exists_appTop_map_eq_zero_of_isLimit`), so
matrices and the matrix identities describing morphisms and their equalities descend to a finite
stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}} {c : Cone E}
  [∀ j, IsAffine (E.obj j)]

/-- **Modules of finite presentation descend to a finite stage, affine case** (Stacks, Tag 01ZR).
Every module of finite presentation on the limit of a cofiltered system of affine schemes is
isomorphic to the pullback of a module of finite presentation on some stage. -/
theorem exists_pullback_iso_of_isLimit_of_isAffine (hc : IsLimit c) (M : c.pt.Modules)
    [M.IsFinitePresentation] :
    ∃ (j : J) (N : (E.obj j).Modules), N.IsFinitePresentation ∧
      Nonempty ((Modules.pullback (c.π.app j)).obj N ≅ M) :=
  sorry

/-- **Equalities of morphisms of modules descend to a finite stage, affine case**
(Stacks, Tag 01ZR). Two morphisms between modules of finite presentation on a stage of a
cofiltered system of affine schemes which agree after pullback to the limit agree after pullback
to some later stage. -/
theorem exists_pullback_map_eq_of_isLimit_of_isAffine (hc : IsLimit c) {j : J}
    {N₁ N₂ : (E.obj j).Modules} [N₁.IsFinitePresentation] [N₂.IsFinitePresentation]
    (ψ₁ ψ₂ : N₁ ⟶ N₂)
    (h : (Modules.pullback (c.π.app j)).map ψ₁ = (Modules.pullback (c.π.app j)).map ψ₂) :
    ∃ (k : J) (t : k ⟶ j),
      (Modules.pullback (E.map t)).map ψ₁ = (Modules.pullback (E.map t)).map ψ₂ :=
  sorry

/-- **Morphisms of modules descend to a finite stage, affine case** (Stacks, Tag 01ZR). Every
morphism between the pullbacks to the limit of two modules of finite presentation on a stage of a
cofiltered system of affine schemes is the pullback of a morphism defined over some later
stage. -/
theorem exists_pullback_map_eq_of_isLimit_of_isAffine' (hc : IsLimit c) {j : J}
    {N₁ N₂ : (E.obj j).Modules} [N₁.IsFinitePresentation] [N₂.IsFinitePresentation]
    (φ : (Modules.pullback (c.π.app j)).obj N₁ ⟶ (Modules.pullback (c.π.app j)).obj N₂) :
    ∃ (k : J) (t : k ⟶ j)
      (ψ : (Modules.pullback (E.map t)).obj N₁ ⟶ (Modules.pullback (E.map t)).obj N₂),
      (pullbackCompOfEq (c.π.app k) (E.map t) (c.π.app j) (c.w t) N₁).inv ≫
        (Modules.pullback (c.π.app k)).map ψ ≫
          (pullbackCompOfEq (c.π.app k) (E.map t) (c.π.app j) (c.w t) N₂).hom = φ :=
  sorry

end AlgebraicGeometry.Scheme.Modules
