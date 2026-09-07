/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Abelian varieties

An abelian variety over a field `K` is a proper, geometrically integral group scheme over `K`.
Following `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, a group scheme over `K` is an object
`G : Over (Spec (.of K))` of the cartesian monoidal category of `K`-schemes together with a
`GrpObj G` structure.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety`: an abelian variety over `K` is a proper, geometrically
  integral group scheme over `K`.

## Main results

Everything in this file is bookkeeping: we record as instances the properties that later files
infer from `IsAbelianVariety G`. Besides the two defining properties themselves, these are that
`G.left` is an integral scheme, that `G` is commutative (`IsCommMonObj G`, hence `CommGrpObj G`),
that `G.hom` is smooth, and that abelian varieties are stable under base change along an
extension of the ground field.

## Dimension convention

The dimension `g` of an abelian variety is deliberately *not* a field of `IsAbelianVariety`, and
no new notion of dimension is introduced here. Since `G.hom` is smooth, use sites carry the
dimension as an instance argument `[SmoothOfRelativeDimension g G.hom]`
(see `Mathlib.AlgebraicGeometry.Morphisms.Smooth`). We make no claim here that such a `g` exists.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- An abelian variety over `K` is a proper, geometrically integral group scheme over `K`. -/
class IsAbelianVariety {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] : Prop where
  isProper : IsProper G.hom
  geometricallyIntegral : GeometricallyIntegral G.hom

attribute [instance] IsAbelianVariety.isProper IsAbelianVariety.geometricallyIntegral

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] [IsAbelianVariety G]

instance : IsIntegral G.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton G.hom

-- The remaining basic properties of an abelian variety are already found by instance
-- resolution from the two defining properties; we record that here.
example : IrreducibleSpace G.left := inferInstance
example : Nonempty G.left := inferInstance
example : IsSeparated G.hom := inferInstance
example : QuasiCompact G.hom := inferInstance
example : LocallyOfFiniteType G.hom := inferInstance

/-- An abelian variety is commutative. -/
instance : IsCommMonObj G :=
  isCommMonObj_of_isProper_of_geometricallyIntegral G

example : CommGrpObj G := inferInstance

/-- An abelian variety is smooth over its base field. -/
instance : Smooth G.hom :=
  haveI : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  smooth_of_grpObj G.hom

/-- Abelian varieties are stable under base change along a morphism `Spec L ⟶ Spec K` of
spectra of fields, i.e. along a field extension `K ⟶ L`. -/
instance {L : Type u} [Field L] (f : Spec (.of L) ⟶ Spec (.of K))
    [GrpObj ((Over.pullback f).obj G)] : IsAbelianVariety ((Over.pullback f).obj G) where
  isProper := by dsimp; infer_instance
  geometricallyIntegral := by dsimp; infer_instance

end AlgebraicGeometry
