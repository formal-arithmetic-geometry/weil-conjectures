/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.PreimageGlue
public import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ModulesAffine

/-!
# Modules of finite presentation descend to a finite stage of a cofiltered limit

Let `{Dⱼ}` be a cofiltered system of quasi-compact separated schemes with affine transition
morphisms and limit `lim Dⱼ`. Every module of finite presentation on `lim Dⱼ` is the pullback of
a module of finite presentation on some stage `Dⱼ` (Stacks, Tag 01ZR; EGA IV₃, 8.5.2).

## Proof

Fix a stage `S = Dᵢ₀` and a finite affine open cover `U a` of `S`. Over each `U a` the system
`{Dⱼᵢ₀⁻¹ U a}` consists of affine schemes, with limit the preimage of `U a` in `lim Dⱼ`, so the
restriction of the module descends to a module `O a` on some stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_of_isLimit_of_isAffine`). Since `S` is
separated, the intersections of the `U a` are affine, so the gluing isomorphisms of the
restrictions on the preimages of `U a ⊓ U b` descend to some stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullHom_eq_of_isLimit_of_isAffine`), and the identity
and cocycle conditions, which hold in the limit, hold at some later stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullHom_eq_pullHom_of_isLimit_of_isAffine`). At that
stage the gluing morphisms define a descent datum for the open cover by the preimages of the
`U a` (`CategoryTheory.Pseudofunctor.DescentData'.ofGlue`), which is effective. The glued
module is of finite presentation, and its pullback to the limit is the original module
(`CategoryTheory.Pseudofunctor.DescentData'.nonempty_map_iso_of_ofGlue`), since morphisms of
modules glue along open covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry

namespace Scheme.Modules

section PullHom

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}} {c : Cone E}
  [∀ j, IsAffine (E.obj j)]

end PullHom

end Scheme.Modules

section Stages

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {i₀ : I}

open Scheme.Modules

end Stages

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

end AlgebraicGeometry
