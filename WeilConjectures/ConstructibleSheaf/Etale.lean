/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constructible sheaves on the small étale site

The specialization of `WeilConjectures.ConstructibleSheaf.Defs` to `P = Q = @Etale`, that
is, to the small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`, which is
definitionally `X.smallGrothendieckTopology @Etale (Q := @Etale)`.

The geometric points are the ones supplied by mathlib: a morphism `Spec Ω ⟶ X` with `Ω` a
separably closed field defines the point `AlgebraicGeometry.Scheme.pointSmallEtale` of the
small étale site, whose fiber functor is `V ↦ Hom_X(Spec Ω, V)`.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}}

/-- A geometric point of `X` is a point of the small étale site of `X`, namely
`AlgebraicGeometry.Scheme.pointSmallEtale`. -/
instance hasGeometricPoints : Scheme.HasGeometricPoints @Etale @Etale where
  point s := Scheme.pointSmallEtale s

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- A sheaf on the small étale site of `X` is *locally constant* if there is an étale cover
of `X` on whose members it becomes constant. -/
abbrev IsLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  Scheme.IsLocallyConstantSheaf @Etale @Etale le_rfl F

end LocallyConstant

section FiniteSheaf

variable {A : Type u'} [Category.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasColimitsOfSize.{u, u} A]

/-- A sheaf on the small étale site of `X` with values in a concrete category is *finite*
if its stalk at every geometric point of `X` is finite. -/
abbrev IsFiniteSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  Scheme.IsFiniteSheaf @Etale @Etale F

end FiniteSheaf

section Constructible

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- A sheaf on the small étale site of `X` with values in a concrete category is *finite
locally constant* if it is locally constant and finite. -/
abbrev IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  Scheme.IsFiniteLocallyConstantSheaf @Etale @Etale le_rfl F

/-- A sheaf on the small étale site of `X` with values in a concrete category is
*constructible* if there is a stratification of `X` such that the pullback of the sheaf to
each stratum is finite locally constant.

For `X` quasi-compact and quasi-separated this global definition agrees with the
affine-local one of [Stacks 03RW]. In the `ℓ`-adic formalism it is applied with
`A = ModuleCat Λ` for the finite ring `Λ = ℤ/ℓⁿℤ`. -/
abbrev IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  Scheme.IsConstructibleSheaf @Etale @Etale le_rfl F

end Constructible

end AlgebraicGeometry.Etale
