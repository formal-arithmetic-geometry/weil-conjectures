/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
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
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions. The only input taken
for granted is that `Rg_*` is a left adjoint for proper `g`; it is *not* assumed that `Rf_!`
is a left adjoint for a general `f`, that is a theorem here.

On the bounded below derived categories, `Rf^!` is *not* defined by another adjoint-functor
argument: it is the restriction of the unbounded `Rf^!` along the inclusion
`DerivedCategory.Plus.ι`, which makes sense because `Rf^!` preserves bounded below objects.
That the restriction is again a right adjoint, now of the bounded below `Rf_!`, is then a
theorem.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isProper` : for `g` proper,
  `Rg_*` is a left adjoint on `D(Z_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[A] ⊣ Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)` for the
  chosen compactification, with scoped notation `R(f)^![A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_ét)`, a consequence of the previous item.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlus` : `Rf^! : D⁺(Y_ét) ⥤ D⁺(X_ét)`, the
  restriction of `R(f)^![A]` to the bounded below derived categories, with scoped notation
  `R(f)^![A]+`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekPlusAdjunction` : the adjunction
  `Rf_! ⊣ Rf^!` on the bounded below derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekPlus` : `Rf_!` is a left
  adjoint on `D⁺(X_ét)`, a consequence of the previous item.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerStar_of_isProper` is `sorry` by design: this file only
  *states* that `Rg_*` has a right adjoint for `g` proper, the proof is left to a later file.
  The adjoint exists by Brown representability, `Rg_*` being, for `g` proper, a colimit
  preserving functor between compactly generated triangulated categories.
* `plus_rightDerivedUpperShriek_obj`, that `Rf^!` preserves bounded below objects, is also
  `sorry` for now.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the instance, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which is why the K-flat hypotheses on the coefficient category `A` of
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` are needed for the
  adjunctions of this file, though not for the definition of `Rf^!` itself.
* By contrast with the unbounded `Rf^!`, the bounded below `R(f)^![A]+` is a restriction of
  `R(f)^![A]`: by `rightDerivedUpperShriekPlusCompatibility` (which is `Iso.refl`) it is
  compatible with the inclusions of the bounded below derived categories by definition. In
  particular there is no ambiguity between "the right adjoint of `Rf_!` on `D⁺`" and "the
  restriction to `D⁺` of the right adjoint of `Rf_!` on `D`".
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

section Proper

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward `Rg_* : D(Z_ét) ⥤ D(Y_ét)` is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper :
    ((g)_*[A]).rightDerivedFunctor.IsLeftAdjoint :=
  sorry

end Proper

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

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

section BoundedBelow

/-- The exceptional inverse image `Rf^!` preserves bounded below objects: if `K ∈ D(Y_ét)`
is bounded below, then so is `Rf^! K ∈ D(X_ét)`.

This is what makes the bounded below `Rf^!` the restriction of the unbounded one. Note that
`Rf^!` is not left t-exact: the bound it produces is shifted by the cohomological amplitude
of `Rf_!`, which is why the statement is about `t.plus` rather than about `IsGE n` for a
fixed `n`. -/
lemma plus_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^![A]).obj K) := sorry

/-- The exceptional inverse image `Rf^! : D⁺(Y_ét) ⥤ D⁺(X_ét)` on the *bounded below* derived
categories of étale sheaves: the restriction of the unbounded `R(f)^![A]` along the inclusions
of the bounded below derived categories, which is well defined by
`plus_rightDerivedUpperShriek_obj`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R(f)^![A])
    (fun K ↦ plus_rightDerivedUpperShriek_obj A f K.obj K.property)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^![" A "]+" =>
  rightDerivedUpperShriekPlus A f

/-- The bounded below `R(f)^![A]+` is compatible with the inclusions of the bounded below
derived categories, by construction. -/
noncomputable def rightDerivedUpperShriekPlusCompatibility :
    R(f)^![A]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)^![A] :=
  ObjectProperty.liftCompιIso _ _ _

end BoundedBelow

section Adjunction

/- The K-flat resolution package on the coefficient category `A`, needed for the derived
adjunction `Di_! ⊣ Di^*` along the open immersion of a compactification, see
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f) : Rf_!(c)[A] ⊣ Rf^!(c)[A] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  rightDerivedUpperShriekOfCompactificationAdjunction A (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` is a left adjoint, its right adjoint
being `R(f)^![A]`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

/-- The adjunction `Rf_! ⊣ Rf^!` on the bounded below derived categories of étale sheaves:
the unbounded adjunction `rightDerivedUpperShriekAdjunction` restricted along the fully
faithful inclusions `DerivedCategory.Plus.ι`, which is legitimate since both `Rf_!` and
`Rf^!` preserve bounded below objects. -/
noncomputable def rightDerivedUpperShriekPlusAdjunction : R(f)_![A]+ ⊣ R(f)^![A]+ :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction A f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (rightDerivedLowerShriekPlusCompatibility A f).symm
    (rightDerivedUpperShriekPlusCompatibility A f).symm

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the bounded below derived
categories is a left adjoint, its right adjoint being `R(f)^![A]+`. -/
instance isLeftAdjoint_rightDerivedLowerShriekPlus : (R(f)_![A]+).IsLeftAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]+).IsRightAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction A f).isRightAdjoint

end Adjunction

end Etale

end AlgebraicGeometry
