/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.Sites.DerivedBrown
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.ProperCoproducts

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *defined* here as a chosen right adjoint of the derived lower shriek `Rf_!` on the
unbounded derived categories of étale sheaves. It is defined whenever `Rf_!` is a left adjoint,
which is taken as an instance argument.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : for torsion coefficients,
  `A = ModuleCat Λ` with `Λ` finite, `Rf_!` is a left adjoint on `D(X_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)`, with scoped
  notation `R(f)^![A]`, for `Rf_!` a left adjoint.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

  below objects, an instance for torsion coefficients and quasi-compact target; and
  below objects, an instance for torsion coefficients; and
  `AlgebraicGeometry.Etale.HasBoundedBelowUpperShrieks`, the same for every `f`.

## Implementation notes

* That `Rf_!` is a left adjoint is *not* true for an arbitrary coefficient category: it rests
  on `Rg_*` preserving coproducts for the proper part `g` of the compactification, which needs
  `Rg_*` to have finite cohomological dimension, i.e. torsion coefficients. For general `A` the
  existence of the right adjoint is therefore an instance argument
  `[(R(f)_![A]).IsLeftAdjoint]` of `rightDerivedUpperShriek`, and it is supplied as an instance
  only at the torsion coefficients `ModuleCat Λ`, `[Finite Λ]`
  (`isLeftAdjoint_rightDerivedLowerShriek`). That instance is the blueprint theorem
  `thm-amb-etale-exceptional-adjoint` of the smooth-purity chapter (Brown representability,
  Stacks `0F5Y`, applied to the coproduct-preserving `Rf_!`). It is proved from Brown
  representability for sheaves of modules
  (`CategoryTheory.Sheaf.isLeftAdjoint_of_preservesCoproducts`)
  and the preservation of coproducts by the proper direct image
  (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`).
* `Rf^!` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint extracted from
  the instance, not a construction. Only the adjunction `rightDerivedUpperShriekAdjunction`
  should be used about it; it has no definitional content.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.
* No bounded below variant of `Rf^!` is defined here. The ambient `Rf^!` preserves `D⁺` only
  through the finite cohomological amplitude of `Rf_!`, and the bounded below exceptional
  functor of the blueprint is the constructible one of `sk-prop-sf-existence` (c). That `Rf^!`
  preserves `D⁺` is recorded, together with the existence of `Rf^!`, by the hypothesis class
  `AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek`, which the pro-étale `Rf^!` assumes; it
  is an instance for torsion coefficients and a quasi-compact target
  (`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`).

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section TorsionCoefficients

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `thm-amb-etale-exceptional-adjoint` and `sk-prop-sf-existence` (a): The ordinary
ambient exceptional adjoint.

For torsion coefficients `Λ`, the derived lower shriek `Rf_! : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` is a
left adjoint; its right adjoint is the exceptional inverse image `Rf^!`.

`Rf_! = D(i_!) ⋙ Rg_*` for the chosen compactification `(i, g)` of `f`. The extension by zero
is exact and commutes with coproducts. For torsion coefficients the proper `Rg_*` has finite
cohomological dimension, locally on `Y` bounded by twice the fibre dimension of `g`, and its
cohomology sheaves commute with filtered colimits, so `Rg_*` preserves coproducts on the
unbounded derived category. Brown representability for the derived category of the
Grothendieck abelian category of étale sheaves of `Λ`-modules (Stacks `0F5Y`) then gives the
right adjoint [SGA 4, Exp. XVIII, Thm 3.1.4].

The blueprint states `sk-prop-sf-existence` (a) for a general Grothendieck abelian coefficient
category, but its proof needs `Rg_*` to preserve coproducts, which blueprint
`lem-amb-proper-coproducts` only provides for torsion coefficients. -/
instance isLeftAdjoint_rightDerivedLowerShriek [Finite Λ] :
    (R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint := by
  let c := HasCompactification.compactification f
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have := adj.isTriangulated_rightAdjoint
  have (K : Type (u + 1)) := preservesColimitsOfShape_rightDerivedLowerStar_of_isProper c.g Λ K
  exact Sheaf.isLeftAdjoint_of_preservesCoproducts _ _
    (D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ]))

end TorsionCoefficients

section Unbounded

variable [(R(f)_![A]).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: *by
definition* a chosen right adjoint of the derived lower shriek `R(f)_![A]`, which is assumed
to be a left adjoint (this holds for torsion coefficients,
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`). -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (R(f)_![A]).rightAdjoint

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  Adjunction.ofIsLeftAdjoint _

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
/-- If `A` is `Λ`-linear, the exceptional inverse image `Rf^!` is `Λ`-linear, being right
adjoint to the `Λ`-linear functor `Rf_!`. -/
instance linear_rightDerivedUpperShriek : (R(f)^![A]).Linear Λ :=
  (rightDerivedUpperShriekAdjunction A f).right_adjoint_linear

end Unbounded

section BoundedBelow

/-- `Rf_!` is a left adjoint whose right adjoint `Rf^!` preserves bounded below objects: if
`K ∈ D(Y_ét)` is bounded below, then so is `Rf^! K ∈ D(X_ét)`.

This is what the constructible pro-étale `Rf^!`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`) needs of the étale one. Neither half
holds for an arbitrary coefficient category: both rest on the finite cohomological amplitude of
the proper direct image, that is, on torsion coefficients, where the class is the instance
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`. Note that `Rf^!` is not left t-exact:
the bound it produces is shifted by the cohomological amplitude of `Rf_!`, which is why the
condition is about `t.plus` rather than about `IsGE n` for a fixed `n`. -/
class HasBoundedBelowUpperShriek : Prop extends (R(f)_![A]).IsLeftAdjoint where
  plus_rightDerivedUpperShriek_obj (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    DerivedCategory.TStructure.t.plus K →
      DerivedCategory.TStructure.t.plus
        ((@Functor.rightAdjoint _ _ _ _ (R(f)_![A]) ⟨exists_rightAdjoint⟩).obj K)

/-- The exceptional inverse image `Rf^!` preserves bounded below objects. -/
lemma plus_rightDerivedUpperShriek_obj [HasBoundedBelowUpperShriek A f]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^![A]).obj K) :=
  HasBoundedBelowUpperShriek.plus_rightDerivedUpperShriek_obj K hK

/-- For torsion coefficients and a quasi-compact target `Y`, `Rf_!` is a left adjoint
(`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`) and `Rf^!` preserves bounded
below objects. The second half holds because `Rf_!` has finite cohomological amplitude, bounded
by twice the fibre dimension of the compactification: if `Rf_!` sends `D^{≤ 0}` into `D^{≤ N}`
then `Rf^!` sends `D^{≥ 0}` into `D^{≥ -N}`, by adjunction [SGA 4, Exp. XVIII, 3.1.7].

The quasi-compactness of `Y` cannot be dropped: it bounds the fibre dimension of the proper
part of the compactification. For `Y = ⨆ₙ Spec k` and `X = ⨆ₙ ℙⁿ_k` over `k` separably closed,
`Rf^! Λ` has the components `Λ[2n](n)`, so it is not bounded below. -/
instance hasBoundedBelowUpperShriek (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [CompactSpace Y] : HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj := sorry

/-- `AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek` for every morphism admitting a
compactification: the coefficients have exceptional inverse images preserving bounded below
objects.

Warning: this is a hypothesis which torsion coefficients do *not* satisfy, since it quantifies
over morphisms with a non-quasi-compact target (see the counterexample in the docstring of
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`). For torsion coefficients, the condition
holds for every `f` with quasi-compact target
(`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`). -/
class HasBoundedBelowUpperShrieks : Prop where
  hasBoundedBelowUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    HasBoundedBelowUpperShriek A f

attribute [instance] HasBoundedBelowUpperShrieks.hasBoundedBelowUpperShriek

end BoundedBelow

end Etale

end AlgebraicGeometry
