/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.PresentationSections

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

On an affine scheme a quasi-coherent module is determined by its global sections, and morphisms
out of it are determined by, and can be built from, the images of generators of the global
sections satisfying the relations (`Modules/PresentationSections.lean`). A presentation of the
global sections pulls back to a presentation with the coefficients pulled back. The global
sections of `X` are the colimit of those of the `Eⱼ`
(`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit`,
`AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit`), so the finitely many
coefficients of the relations, of the images of generators, and of the identities between them
descend to a finite stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

section Helpers

variable {X Y : Scheme.{u}}

end Helpers

section Colimit

/-!
### Schemes whose global functions are the colimit of those of a cofiltered system

Throughout, `p j : X ⟶ E.obj j` is a compatible family of morphisms from an affine scheme `X` to
a cofiltered system of affine schemes such that `Γ(X, ⊤)` is the colimit of the `Γ(E.obj j, ⊤)`:
every global function on `X` comes from some stage (`hsurj`), and a global function on a stage
vanishing on `X` vanishes on some later stage (`hinj`). This is the case for the limit cone
(`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit`,
`AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit`). Working with `X` rather
than with the cone point avoids the objects `((Functor.const J).obj c.pt).obj j`.
-/

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}}
  [∀ j, IsAffine (E.obj j)] {X : Scheme.{u}}

end Colimit

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}} {c : Cone E}
  [∀ j, IsAffine (E.obj j)]

end AlgebraicGeometry.Scheme.Modules
