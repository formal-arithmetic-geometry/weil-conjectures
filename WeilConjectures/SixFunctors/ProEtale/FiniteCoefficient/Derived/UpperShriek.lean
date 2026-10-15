/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenImmersionLowerShriek

/-!

# Derived Upper Shriek

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *constructed* here out of the two halves of the derived lower shriek
`Rf_! = Di_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:

`Rf^! := Rg^! ⋙ Di^*`,

where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` along the *proper*
morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`, which is right
adjoint to `Di_!` by `ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions. The only input taken
for granted is that `Rg_*` is a left adjoint for proper `g`; it is *not* assumed that `Rf_!`
is a left adjoint for a general `f`, that is a theorem here.

`Rf^!` is only defined on the unbounded derived categories: it does not preserve bounded
below objects in general, so it does not restrict to `D⁺`.

# Main Results

- `AlgebraicGeometry.ProEtale.isLeftAdjoint_rightDerivedLowerStar_of_isProper` : for `g` proper,
  `Rg_*` is a left adjoint on `D(Z_proét)`.

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[A]`.

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[A] ⊣ Rf^!(c)[A]`.

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek` : `Rf^! : D(Y_proét) ⥤ D(X_proét)` for the
  chosen compactification, with scoped notation `R(f)^![A]`.

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.ProEtale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_proét)`, a consequence of the previous item.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerStar_of_isProper` is `sorry` by design: this file only
  *states* that `Rg_*` has a right adjoint for `g` proper, the proof is left to a later file.
  The adjoint exists by Brown representability, `Rg_*` being, for `g` proper, a colimit
  preserving functor between compactly generated triangulated categories.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the instance, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which is why the K-flat hypotheses on the coefficient category `A` of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenImmersionLowerShriek` are
  needed for the adjunctions of this file, though not for the definition of `Rf^!` itself.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` weakly étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

section Proper

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward `Rg_* : D(Z_proét) ⥤ D(Y_proét)` is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper :
    ((g)_*[A]).rightDerivedFunctor.IsLeftAdjoint :=
  sorry

end Proper

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The exceptional inverse image `Rf^! : D(Y_proét) ⥤ D(X_proét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of pro-étale sheaves: a chosen
right adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the
levelwise pullback `Di^*` along the open immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  ((c.g)_*[A]).rightDerivedFunctor.rightAdjoint ⋙ D((c.i)^*[A])

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!("c")[" A "]" =>
  rightDerivedUpperShriekOfCompactification A c

end OfCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Y_proét) ⥤ D(X_proét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of pro-étale sheaves: the
functor `rightDerivedUpperShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
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
`ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f) : Rf_!(c)[A] ⊣ Rf^!(c)[A] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of pro-étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  rightDerivedUpperShriekOfCompactificationAdjunction A (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_! : D(X_proét) ⥤ D(Y_proét)` is a left adjoint, its right adjoint
being `R(f)^![A]`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

end Adjunction

end ProEtale

end AlgebraicGeometry
