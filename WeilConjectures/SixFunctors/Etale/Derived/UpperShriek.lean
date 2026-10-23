/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *constructed* here out of the two halves of the derived lower shriek
`Rf_! = Di_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:

`Rf^! := Rg^! ⋙ Di^*`,

where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` along the *proper*
morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`, which is right
adjoint to `Di_!` by `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions. The only input is that
`Rg_*` is a left adjoint for the proper part `g` of the compactification. This does not hold
for arbitrary coefficients, so it is an explicit hypothesis
`[((c.g)_*[A]).rightDerivedFunctor.IsLeftAdjoint]`, not an instance (see the implementation
notes).

`Rf^!` is only defined on the unbounded derived categories: it does not preserve bounded
below objects in general, so it does not restrict to `D⁺`.

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[A] ⊣ Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)` for the
  chosen compactification, with scoped notation `R(f)^![A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_ét)` when `Rg_*` is one for the proper part `g` of the chosen compactification, a
  consequence of the previous item.

All of these take the hypothesis that `Rg_*` is a left adjoint.

## Implementation notes

* That `Rg_*` is a left adjoint for `g` proper is a hypothesis, not an instance. By Brown
  representability it holds when `Rg_*` preserves coproducts between compactly generated
  triangulated categories, e.g. for torsion coefficients and `g` of finite cohomological
  dimension. For arbitrary Grothendieck abelian coefficients and arbitrary schemes, `Rg_*` need
  not preserve coproducts on the unbounded derived category. The pro-étale analogue is false in
  general, see `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek`.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the hypothesis, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which is why the K-flat hypotheses on the coefficient category `A` of
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` are needed for the
  adjunctions of this file, though not for the definition of `Rf^!` itself.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

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

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [((c.g)_*[A]).rightDerivedFunctor.IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: a chosen
right adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the
levelwise pullback `Di^*` along the open immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  ((c.g)_*[A]).rightDerivedFunctor.rightAdjoint ⋙ D((c.i)^*[A])

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!("c")[" A "]" =>
  rightDerivedUpperShriekOfCompactification A c

end OfCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [(((HasCompactification.compactification f).g)_*[A]).rightDerivedFunctor.IsLeftAdjoint]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `rightDerivedUpperShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  Rf^!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

lemma rightDerivedUpperShriek_eq : R(f)^![A] =
    Rf^!(HasCompactification.compactification f)[A] := rfl

end Unbounded

section Adjunction

/- The K-flat resolution package on the coefficient category `A`, needed for the derived
adjunction `Di_! ⊣ Di^*` along the open immersion of a compactification, see
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`, provided `Rg_*` is a left adjoint. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f) [((c.g)_*[A]).rightDerivedFunctor.IsLeftAdjoint] :
    Rf_!(c)[A] ⊣ Rf^!(c)[A] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  rightDerivedUpperShriekOfCompactificationAdjunction A (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` is a left adjoint, its right adjoint
being `R(f)^![A]`, provided `Rg_*` is a left adjoint for the proper part `g` of the chosen
compactification. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

end Adjunction

end Etale

end AlgebraicGeometry
